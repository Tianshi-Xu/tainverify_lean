/- Auto-generated pattern proof file.
   Pattern: 78
   Hash: 2c9154fd373a643c
   Goals: 140, 175, 178, 254

   Structure:
     SM has a single `BW_linear` node `ins := [gOutTid, xTid, wTid], outs := [dxTid, dwTid]`.
     PM has 4 `BW_linear` nodes (one per rank), one `AllReducePrim` collecting their `dx`
     outputs into PM tid = SM tid, then 4 `ChunkPrim` nodes dim=1 distributing the result.

     The proof uses `bw_linear_3d_fst_row_parallel` (Denote.lean:4362) to bridge
     `(bw_linear (gather g) x (gather w)).1 = allReducePrim numParts 0 [per-rank bw_linear.1]`.
     Then a `chunk-then-allGather-dim1 = id` identity closes the reconstruction.
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Pattern_21
import denote.gpt_ly4_segments.Pattern_35
import denote.gpt_ly4_segments.Pattern_79
import denote.gpt_ly4_segments.Pattern_98
import denote.gpt_ly4_segments.Pattern_99
import denote.gpt_ly4_segments.Pattern_126

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_78_goalIds : List Nat := [140, 175, 178, 254]
inductive pattern_78_target : Prop → Prop
  | goal_140 : pattern_78_target goal_140_stmt
  | goal_175 : pattern_78_target goal_175_stmt
  | goal_178 : pattern_78_target goal_178_stmt
  | goal_254 : pattern_78_target goal_254_stmt

def pattern_78_stmt : Prop :=
  ∀ {target : Prop}, pattern_78_target target → target

set_option maxRecDepth 16384
set_option maxHeartbeats 400000000

/-! ## Generic per-node `denoteGraph` step lemmas (mirror Pattern_126:55). -/

private theorem denote_bw_linear_fst_step (g : GraphDecl) (initStore : Store)
    (K : Nat) (gTid xTid wTid dxTid dwTid : Tid) (rk : Nat)
    (node : NodeDecl)
    (hnode : node = { rank := rk, op := "OpName.BW_linear",
                      ins := [gTid, xTid, wTid], outs := [dxTid, dwTid] })
    (hne : dxTid ≠ dwTid)
    (hKlt : K < g.nodes.length)
    (hidx : g.nodes[K]'hKlt = node)
    (hsuf_out : ∀ n ∈ g.nodes.drop (K+1), dxTid ∉ n.outs)
    (hsuf_g : ∀ n ∈ g.nodes.drop K, gTid ∉ n.outs)
    (hsuf_x : ∀ n ∈ g.nodes.drop K, xTid ∉ n.outs)
    (hsuf_w : ∀ n ∈ g.nodes.drop K, wTid ∉ n.outs) :
    denoteGraph g initStore dxTid =
      (bw_linear (denoteGraph g initStore gTid) (denoteGraph g initStore xTid)
                 (denoteGraph g initStore wTid)).1 := by
  have h1 : denoteGraph g initStore dxTid =
      denoteGraph { g with nodes := g.nodes.take (K+1) } initStore dxTid :=
    denoteGraph_tid_eq_of_suffix_no_writes g initStore dxTid
      (g.nodes.take (K+1)) (g.nodes.drop (K+1))
      (List.take_append_drop (K+1) _).symm hsuf_out
  rw [h1]
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
  rw [hnode, applyNode_bw_linear_fst_out g _ rk gTid xTid wTid dxTid dwTid hne]
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
  rw [hg, hx, hw]

private theorem denote_allReducePrim_step (g : GraphDecl) (initStore : Store)
    (K : Nat) (ins : List Tid) (outTid : Tid) (rk : Nat)
    (node : NodeDecl)
    (hnode : node = { rank := rk, op := "OpName.AllReducePrim",
                      ins := ins, outs := [outTid] })
    (hKlt : K < g.nodes.length)
    (hidx : g.nodes[K]'hKlt = node)
    (hsuf_out : ∀ n ∈ g.nodes.drop (K+1), outTid ∉ n.outs)
    (hsuf_ins : ∀ t ∈ ins, ∀ n ∈ g.nodes.drop K, t ∉ n.outs) :
    denoteGraph g initStore outTid =
      allReducePrim g.numRanks rk (ins.map (denoteGraph g initStore)) := by
  have h1 : denoteGraph g initStore outTid =
      denoteGraph { g with nodes := g.nodes.take (K+1) } initStore outTid :=
    denoteGraph_tid_eq_of_suffix_no_writes g initStore outTid
      (g.nodes.take (K+1)) (g.nodes.drop (K+1))
      (List.take_append_drop (K+1) _).symm hsuf_out
  rw [h1]
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
  rw [hnode, applyNode_allReducePrim_out g _ rk ins outTid]
  -- Replace stores at each input tid by the full denoteGraph.
  have hmap_eq : (ins.map (denoteGraph { g with nodes := g.nodes.take K } initStore)) =
      ins.map (denoteGraph g initStore) := by
    apply List.map_congr_left
    intro t ht
    exact (denoteGraph_tid_eq_of_suffix_no_writes g initStore t
      (g.nodes.take K) (g.nodes.drop K)
      (List.take_append_drop K _).symm (hsuf_ins t ht)).symm
  rw [hmap_eq]

private theorem denote_chunkPrim_step (g : GraphDecl) (initStore : Store)
    (K : Nat) (inTid outTid : Tid) (rk dim : Nat)
    (node : NodeDecl)
    (hnode : node = { rank := rk, op := "OpName.ChunkPrim",
                      ins := [inTid], outs := [outTid], params := [dim] })
    (hKlt : K < g.nodes.length)
    (hidx : g.nodes[K]'hKlt = node)
    (hsuf_out : ∀ n ∈ g.nodes.drop (K+1), outTid ∉ n.outs)
    (hsuf_in : ∀ n ∈ g.nodes.drop K, inTid ∉ n.outs) :
    denoteGraph g initStore outTid =
      chunkPrimDimN dim g.numRanks rk (denoteGraph g initStore inTid) := by
  have h1 : denoteGraph g initStore outTid =
      denoteGraph { g with nodes := g.nodes.take (K+1) } initStore outTid :=
    denoteGraph_tid_eq_of_suffix_no_writes g initStore outTid
      (g.nodes.take (K+1)) (g.nodes.drop (K+1))
      (List.take_append_drop (K+1) _).symm hsuf_out
  rw [h1]
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
  rw [hnode, applyNode_chunkPrimDimN_out g _ rk inTid outTid dim]
  have hin : (denoteGraph { g with nodes := g.nodes.take K } initStore) inTid =
      denoteGraph g initStore inTid :=
    (denoteGraph_tid_eq_of_suffix_no_writes g initStore inTid
      (g.nodes.take K) (g.nodes.drop K)
      (List.take_append_drop K _).symm hsuf_in).symm
  rw [hin]

private theorem denote_init_tid (g : GraphDecl) (initStore : Store) (tid : Tid)
    (hno : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraph g initStore tid = initStore tid := by
  have h := denoteGraph_tid_eq_of_suffix_no_writes g initStore tid
    [] g.nodes (by simp) hno
  rw [h]
  have heq : ({ g with nodes := [] } : GraphDecl) =
      { numRanks := g.numRanks, nodes := [] } := by cases g; rfl
  rw [heq, denoteGraph_nodes_nil]

/-! ## chunk-then-allGather identity along dim 1 for `[1, 8, 32]` tensors. -/

private theorem chunkPrimDimN_1_4_shape (y : Tensor) (d r : Nat)
    (hy : y.shape = [1, 8, d]) :
    (chunkPrimDimN 1 4 r y).shape = [1, 2, d] := by
  rw [chunkPrimDimN_shape 1 4 r _ _ hy (by omega)]
  simp [List.set, List.getD]

/-- Specialized `valAt` for `chunkPrimDimN dim=1 numParts=4` on shape `[1,8,128]`.
    Local mirror of `chunk_dim1_4_1_8_32_valAt` with 128 in place of 32. -/
private theorem chunk_dim1_4_1_8_128_valAt (x : Tensor) (r p j : Nat)
    (hx : x.shape = [1, 8, 128]) (hr : r < 4) (hp : p < 2) (hj : j < 128) :
    valAt (chunkPrimDimN 1 4 r x) (p * 128 + j) = valAt x ((r * 2 + p) * 128 + j) := by
  have hloc : p * 128 + j < 256 := by
    have : p * 128 ≤ 1 * 128 := Nat.mul_le_mul_right 128 (by omega)
    omega
  have hchunk_shape : (chunkPrimDimN 1 4 r x).shape = [1, 2, 128] := by
    rw [chunkPrimDimN_shape 1 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hloc_shape : p * 128 + j < prodShape (chunkPrimDimN 1 4 r x).shape := by
    rw [hchunk_shape]; simp [prodShape]; exact hloc
  rw [valAt_of_lt _ _ hloc_shape]
  unfold chunkPrimDimN Tensor.mkShape
  simp only [hx, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (4 : Nat) ≠ 0 by omega, show (128 : Nat) ≠ 0 by omega,
    show (8 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 0 by omega,
    show (1 : Nat) ≠ 0 by omega, ite_false]
  congr 1
  have hrm : r % 4 = r := Nat.mod_eq_of_lt hr
  rw [hrm]
  have hsum : p * 128 + j < 256 := hloc
  have h1 : (8 / 4 : Nat) = 2 := by norm_num
  have h2 : (1 * 128 : Nat) = 128 := by norm_num
  have h3 : (8 * (1 * 128) : Nat) = 1024 := by norm_num
  have h4 : (2 * (1 * 128) : Nat) = 256 := by norm_num
  simp only [h1, h2, h3, h4, show (256 : Nat) ≠ 0 by omega, show (128 : Nat) ≠ 0 by omega,
    ite_false]
  have hd : (p * 128 + j) / 256 = 0 := Nat.div_eq_of_lt hsum
  have hm : (p * 128 + j) % 256 = p * 128 + j := Nat.mod_eq_of_lt hsum
  rw [hd, hm]
  have h5 : (p * 128 + j) / 128 = p := by omega
  have h6 : (p * 128 + j) % 128 = j := by omega
  rw [h5, h6]
  ring

/-- `valAt` of `allGatherPrimDimN 1 4 0 xs` for `[1, 2, 32]` shards.
    Inline analog of `Common.valAt_ag1_16_2_64_16`. -/
private lemma valAt_ag1_1_8_32 (xs : List Tensor) (idx : Nat)
    (hhead : (xs.head?.map (·.shape)).getD [] = [1, 2, 32])
    (hidx : idx < 256) :
    valAt (allGatherPrimDimN 1 4 0 xs) idx =
      valAt (xs[idx / 64]?.getD (zeroTensor [1, 2, 32]))
            (idx % 64) := by
  have hshape_out : (allGatherPrimDimN 1 4 0 xs).shape = [1, 8, 32] := by
    have := allGatherPrimDimN_shape 1 4 xs [1, 2, 32] hhead
    simpa [List.set, List.getD] using this
  have hidx_prod : idx < prodShape (allGatherPrimDimN 1 4 0 xs).shape := by
    rw [hshape_out]; simpa [prodShape] using hidx
  rw [valAt_of_lt _ _ hidx_prod]
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead,
    List.getD, List.drop, List.foldl,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  simp only [show (1 : Nat) * 32 = 32 from by norm_num,
    show (2 : Nat) * 4 = 8 from by norm_num,
    show (8 : Nat) * 32 = 256 from by norm_num,
    show (2 : Nat) * 32 = 64 from by norm_num,
    show (1 : Nat) * 256 = 256 from by norm_num,
    show (256 : Nat) ≠ 0 by omega, show (32 : Nat) ≠ 0 by omega,
    show (2 : Nat) ≠ 0 by omega, show (64 : Nat) ≠ 0 by omega,
    ite_false]
  have hdiv256 : idx / 256 = 0 := Nat.div_eq_of_lt hidx
  have hmod256 : idx % 256 = idx := Nat.mod_eq_of_lt hidx
  rw [hdiv256, hmod256]
  -- Goal:
  -- valAt (xs[idx / 32 / 2]?.getD (zeroTensor [1, 2, 32])) (0 * 64 + idx / 32 % 2 * 32 + idx % 32)
  --   = valAt (xs[idx / 64]?.getD (zeroTensor [1, 2, 32])) (idx % 64)
  have hidx_eq : idx / 32 / 2 = idx / 64 := by omega
  have hloc_eq : 0 * 64 + idx / 32 % 2 * 32 + idx % 32 = idx % 64 := by omega
  rw [hidx_eq, hloc_eq]

private theorem gather_chunk_dim1_1_8_32 (y : Tensor)
    (hy : y.shape = [1, 8, 32]) :
    allGatherPrimDimN 1 4 0
      [chunkPrimDimN 1 4 0 y, chunkPrimDimN 1 4 1 y,
       chunkPrimDimN 1 4 2 y, chunkPrimDimN 1 4 3 y] = y := by
  set xs : List Tensor :=
    [chunkPrimDimN 1 4 0 y, chunkPrimDimN 1 4 1 y,
     chunkPrimDimN 1 4 2 y, chunkPrimDimN 1 4 3 y] with hxs_def
  have hchunk_sh : ∀ r, (chunkPrimDimN 1 4 r y).shape = [1, 2, 32] := fun r =>
    chunkPrimDimN_1_4_shape y 32 r hy
  have hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 2, 32] := by
    simp [xs, hchunk_sh 0]
  have hgather_sh : (allGatherPrimDimN 1 4 0 xs).shape = [1, 8, 32] := by
    have := allGatherPrimDimN_shape 1 4 xs [1, 2, 32] hhead
    simpa [List.set, List.getD] using this
  apply Tensor.ext (by rw [hgather_sh, hy])
  intro idx hidx
  have hidx_lt : idx < 256 := by
    have hh : idx < prodShape (allGatherPrimDimN 1 4 0 xs).shape := hidx
    rw [hgather_sh] at hh
    simpa [prodShape] using hh
  rw [valAt_ag1_1_8_32 xs idx hhead hidx_lt]
  -- Selected piece: idx/64; case split.
  have hp_range : idx / 64 = 0 ∨ idx / 64 = 1 ∨ idx / 64 = 2 ∨ idx / 64 = 3 := by omega
  have hp1_lt : idx % 64 / 32 < 2 := by omega
  have hp2_lt : idx % 32 < 32 := Nat.mod_lt _ (by omega)
  have hidx_decomp : idx % 64 = (idx % 64 / 32) * 32 + idx % 32 := by omega
  rcases hp_range with h | h | h | h
  · rw [h]; show valAt (chunkPrimDimN 1 4 0 y) (idx % 64) = _
    rw [hidx_decomp,
        chunk_dim1_4_1_8_32_valAt y 0 (idx % 64 / 32) (idx % 32) hy
          (by omega) hp1_lt hp2_lt]
    congr 1; omega
  · rw [h]; show valAt (chunkPrimDimN 1 4 1 y) (idx % 64) = _
    rw [hidx_decomp,
        chunk_dim1_4_1_8_32_valAt y 1 (idx % 64 / 32) (idx % 32) hy
          (by omega) hp1_lt hp2_lt]
    congr 1; omega
  · rw [h]; show valAt (chunkPrimDimN 1 4 2 y) (idx % 64) = _
    rw [hidx_decomp,
        chunk_dim1_4_1_8_32_valAt y 2 (idx % 64 / 32) (idx % 32) hy
          (by omega) hp1_lt hp2_lt]
    congr 1; omega
  · rw [h]; show valAt (chunkPrimDimN 1 4 3 y) (idx % 64) = _
    rw [hidx_decomp,
        chunk_dim1_4_1_8_32_valAt y 3 (idx % 64 / 32) (idx % 32) hy
          (by omega) hp1_lt hp2_lt]
    congr 1; omega

/-! ## chunk-then-allGather identity along dim 1 for `[1, 8, 128]` tensors. -/

private lemma valAt_ag1_1_8_128 (xs : List Tensor) (idx : Nat)
    (hhead : (xs.head?.map (·.shape)).getD [] = [1, 2, 128])
    (hidx : idx < 1024) :
    valAt (allGatherPrimDimN 1 4 0 xs) idx =
      valAt (xs[idx / 256]?.getD (zeroTensor [1, 2, 128]))
            (idx % 256) := by
  have hshape_out : (allGatherPrimDimN 1 4 0 xs).shape = [1, 8, 128] := by
    have := allGatherPrimDimN_shape 1 4 xs [1, 2, 128] hhead
    simpa [List.set, List.getD] using this
  have hidx_prod : idx < prodShape (allGatherPrimDimN 1 4 0 xs).shape := by
    rw [hshape_out]; simpa [prodShape] using hidx
  rw [valAt_of_lt _ _ hidx_prod]
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead,
    List.getD, List.drop, List.foldl,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  simp only [show (1 : Nat) * 128 = 128 from by norm_num,
    show (2 : Nat) * 4 = 8 from by norm_num,
    show (8 : Nat) * 128 = 1024 from by norm_num,
    show (2 : Nat) * 128 = 256 from by norm_num,
    show (1 : Nat) * 1024 = 1024 from by norm_num,
    show (1024 : Nat) ≠ 0 by omega, show (128 : Nat) ≠ 0 by omega,
    show (2 : Nat) ≠ 0 by omega, show (256 : Nat) ≠ 0 by omega,
    ite_false]
  have hdiv : idx / 1024 = 0 := Nat.div_eq_of_lt hidx
  have hmod : idx % 1024 = idx := Nat.mod_eq_of_lt hidx
  rw [hdiv, hmod]
  have hidx_eq : idx / 128 / 2 = idx / 256 := by omega
  have hloc_eq : 0 * 256 + idx / 128 % 2 * 128 + idx % 128 = idx % 256 := by omega
  rw [hidx_eq, hloc_eq]

private theorem gather_chunk_dim1_1_8_128 (y : Tensor)
    (hy : y.shape = [1, 8, 128]) :
    allGatherPrimDimN 1 4 0
      [chunkPrimDimN 1 4 0 y, chunkPrimDimN 1 4 1 y,
       chunkPrimDimN 1 4 2 y, chunkPrimDimN 1 4 3 y] = y := by
  set xs : List Tensor :=
    [chunkPrimDimN 1 4 0 y, chunkPrimDimN 1 4 1 y,
     chunkPrimDimN 1 4 2 y, chunkPrimDimN 1 4 3 y] with hxs_def
  have hchunk_sh : ∀ r, (chunkPrimDimN 1 4 r y).shape = [1, 2, 128] := fun r =>
    chunkPrimDimN_1_4_shape y 128 r hy
  have hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 2, 128] := by
    simp [xs, hchunk_sh 0]
  have hgather_sh : (allGatherPrimDimN 1 4 0 xs).shape = [1, 8, 128] := by
    have := allGatherPrimDimN_shape 1 4 xs [1, 2, 128] hhead
    simpa [List.set, List.getD] using this
  apply Tensor.ext (by rw [hgather_sh, hy])
  intro idx hidx
  have hidx_lt : idx < 1024 := by
    have hh : idx < prodShape (allGatherPrimDimN 1 4 0 xs).shape := hidx
    rw [hgather_sh] at hh
    simpa [prodShape] using hh
  rw [valAt_ag1_1_8_128 xs idx hhead hidx_lt]
  have hp_range : idx / 256 = 0 ∨ idx / 256 = 1 ∨ idx / 256 = 2 ∨ idx / 256 = 3 := by omega
  have hp1_lt : idx % 256 / 128 < 2 := by omega
  have hp2_lt : idx % 128 < 128 := Nat.mod_lt _ (by omega)
  have hidx_decomp : idx % 256 = (idx % 256 / 128) * 128 + idx % 128 := by omega
  rcases hp_range with h | h | h | h
  · rw [h]; show valAt (chunkPrimDimN 1 4 0 y) (idx % 256) = _
    rw [hidx_decomp,
        chunk_dim1_4_1_8_128_valAt y 0 (idx % 256 / 128) (idx % 128) hy
          (by omega) hp1_lt hp2_lt]
    congr 1; omega
  · rw [h]; show valAt (chunkPrimDimN 1 4 1 y) (idx % 256) = _
    rw [hidx_decomp,
        chunk_dim1_4_1_8_128_valAt y 1 (idx % 256 / 128) (idx % 128) hy
          (by omega) hp1_lt hp2_lt]
    congr 1; omega
  · rw [h]; show valAt (chunkPrimDimN 1 4 2 y) (idx % 256) = _
    rw [hidx_decomp,
        chunk_dim1_4_1_8_128_valAt y 2 (idx % 256 / 128) (idx % 128) hy
          (by omega) hp1_lt hp2_lt]
    congr 1; omega
  · rw [h]; show valAt (chunkPrimDimN 1 4 3 y) (idx % 256) = _
    rw [hidx_decomp,
        chunk_dim1_4_1_8_128_valAt y 3 (idx % 256 / 128) (idx % 128) hy
          (by omega) hp1_lt hp2_lt]
    congr 1; omega

/-! ## Bridge for dX with numParts=4 (literal 4-element lists).

    Wraps `bw_linear_3d_fst_row_parallel` over clean `Tensor` parameters so that
    elaboration at the goal_140/175/254 sites avoids the WHNF blow-up that occurs
    when the general lemma is applied directly to `denoteGraph` terms. -/

private theorem bridge_dX_4
    (B S shard_o iX : Nat)
    (g0 g1 g2 g3 x w0 w1 w2 w3 : Tensor)
    (hg0 : g0.shape = [B, S, shard_o]) (hg1 : g1.shape = [B, S, shard_o])
    (hg2 : g2.shape = [B, S, shard_o]) (hg3 : g3.shape = [B, S, shard_o])
    (hw0 : w0.shape = [shard_o, iX]) (hw1 : w1.shape = [shard_o, iX])
    (hw2 : w2.shape = [shard_o, iX]) (hw3 : w3.shape = [shard_o, iX])
    (hx : x.shape = [B, S, iX])
    (hshard_o : 0 < shard_o) (hBS : 0 < B * S) :
    (bw_linear (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]) x
       (allGatherPrimDimN 0 4 0 [w0, w1, w2, w3])).1 =
      allReducePrim 4 0
        [(bw_linear g0 x w0).1, (bw_linear g1 x w1).1,
         (bw_linear g2 x w2).1, (bw_linear g3 x w3).1] := by
  have hgs_shapes : ∀ g ∈ ([g0, g1, g2, g3] : List Tensor), g.shape = [B, S, shard_o] := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h
    · rw [h]; exact hg0
    · rw [h]; exact hg1
    · rw [h]; exact hg2
    · rw [h]; exact hg3
  have hws_shapes : ∀ w ∈ ([w0, w1, w2, w3] : List Tensor), w.shape = [shard_o, iX] := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h
    · rw [h]; exact hw0
    · rw [h]; exact hw1
    · rw [h]; exact hw2
    · rw [h]; exact hw3
  have h := bw_linear_3d_fst_row_parallel 4 B S (shard_o * 4) iX shard_o
    [g0, g1, g2, g3] x [w0, w1, w2, w3] rfl rfl hgs_shapes hx hws_shapes
    (by ring) (by decide) hshard_o hBS
  rw [h]
  rfl

/-! ## Per-goal proofs.

We work pattern-by-pattern. Each goal needs ~150 LOC. We share the
generic step lemmas and the chunk-gather identity above.

Per-tid `denoteGraph` evaluations are extracted into named `private theorem`s.
This matches the structure of `Pattern_76.lean` and isolates each `(by decide)`
call into its own elaboration scope, preventing the kernel-whnf hot spot that
arises when many large `Decidable.isTrue` proof terms accumulate in a single
declaration.
-/

/-! ### Goal 140

  SM tid 758 = `bw_linear gradOut x w` with gradOut=760, x=596, w=597.
  PM ranks 0..3 produce `bw_linear (g_r) x (w_r)` at PM tids 1582/1579/1576/1573
  (with gradOut shards 1575/1578/1581/1584, w shards 1557/1558/1559/1560).
  PM tid 758 = `allReducePrim 4 0 [pm 1582, pm 1579, pm 1576, pm 1573]`.
  PM tids 1544/1548/1552/1556 = `chunkPrimDimN 1 4 r (pm 758)`.

  SM node `outs := [758, 759]` is at SM index 208.
  PM BW_linear at indices 1385..1388, AR at 1389, Chunks at 1390..1393.
-/

@[reducible] private def sm_n208 : NodeDecl :=
  { rank := 0, op := "OpName.BW_linear", ins := [760, 596, 597], outs := [758, 759] }

@[reducible] private def pm140_n1385 : NodeDecl :=
  { rank := 0, op := "OpName.BW_linear", ins := [1575, 596, 1557], outs := [1582, 1574] }
@[reducible] private def pm140_n1386 : NodeDecl :=
  { rank := 1, op := "OpName.BW_linear", ins := [1578, 596, 1558], outs := [1579, 1577] }
@[reducible] private def pm140_n1387 : NodeDecl :=
  { rank := 2, op := "OpName.BW_linear", ins := [1581, 596, 1559], outs := [1576, 1580] }
@[reducible] private def pm140_n1388 : NodeDecl :=
  { rank := 3, op := "OpName.BW_linear", ins := [1584, 596, 1560], outs := [1573, 1583] }
@[reducible] private def pm140_n1389 : NodeDecl :=
  { rank := 0, op := "OpName.AllReducePrim", ins := [1582, 1579, 1576, 1573], outs := [758] }
@[reducible] private def pm140_n1390 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [758], outs := [1544], params := [1] }
@[reducible] private def pm140_n1391 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [758], outs := [1548], params := [1] }
@[reducible] private def pm140_n1392 : NodeDecl :=
  { rank := 2, op := "OpName.ChunkPrim", ins := [758], outs := [1552], params := [1] }
@[reducible] private def pm140_n1393 : NodeDecl :=
  { rank := 3, op := "OpName.ChunkPrim", ins := [758], outs := [1556], params := [1] }

/-! #### Per-tid evaluation helpers for goal_140. -/

private theorem sm140_eval_758 (initSM : Store) :
    denoteGraph sm initSM 758 =
      (bw_linear (denoteGraph sm initSM 760) (denoteGraph sm initSM 596)
                 (denoteGraph sm initSM 597)).1 := by
  apply denote_bw_linear_fst_step sm initSM 208 760 596 597 758 759 0 sm_n208 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm140_eval_1582 (initPM : Store) :
    denoteGraph pm initPM 1582 =
      (bw_linear (denoteGraph pm initPM 1575) (denoteGraph pm initPM 596)
                 (denoteGraph pm initPM 1557)).1 := by
  apply denote_bw_linear_fst_step pm initPM 1385 1575 596 1557 1582 1574 0 pm140_n1385 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm140_eval_1579 (initPM : Store) :
    denoteGraph pm initPM 1579 =
      (bw_linear (denoteGraph pm initPM 1578) (denoteGraph pm initPM 596)
                 (denoteGraph pm initPM 1558)).1 := by
  apply denote_bw_linear_fst_step pm initPM 1386 1578 596 1558 1579 1577 1 pm140_n1386 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm140_eval_1576 (initPM : Store) :
    denoteGraph pm initPM 1576 =
      (bw_linear (denoteGraph pm initPM 1581) (denoteGraph pm initPM 596)
                 (denoteGraph pm initPM 1559)).1 := by
  apply denote_bw_linear_fst_step pm initPM 1387 1581 596 1559 1576 1580 2 pm140_n1387 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm140_eval_1573 (initPM : Store) :
    denoteGraph pm initPM 1573 =
      (bw_linear (denoteGraph pm initPM 1584) (denoteGraph pm initPM 596)
                 (denoteGraph pm initPM 1560)).1 := by
  apply denote_bw_linear_fst_step pm initPM 1388 1584 596 1560 1573 1583 3 pm140_n1388 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm140_eval_758 (initPM : Store) :
    denoteGraph pm initPM 758 = allReducePrim pm.numRanks 0
      ([1582, 1579, 1576, 1573].map (denoteGraph pm initPM)) := by
  apply denote_allReducePrim_step pm initPM 1389 [1582, 1579, 1576, 1573] 758 0 pm140_n1389 rfl
    (by decide) (by decide) (by decide)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl <;> decide

private theorem pm140_eval_1544 (initPM : Store) :
    denoteGraph pm initPM 1544 = chunkPrimDimN 1 pm.numRanks 0 (denoteGraph pm initPM 758) := by
  apply denote_chunkPrim_step pm initPM 1390 758 1544 0 1 pm140_n1390 rfl
    (by decide) (by decide) (by decide) (by decide)

private theorem pm140_eval_1548 (initPM : Store) :
    denoteGraph pm initPM 1548 = chunkPrimDimN 1 pm.numRanks 1 (denoteGraph pm initPM 758) := by
  apply denote_chunkPrim_step pm initPM 1391 758 1548 1 1 pm140_n1391 rfl
    (by decide) (by decide) (by decide) (by decide)

private theorem pm140_eval_1552 (initPM : Store) :
    denoteGraph pm initPM 1552 = chunkPrimDimN 1 pm.numRanks 2 (denoteGraph pm initPM 758) := by
  apply denote_chunkPrim_step pm initPM 1392 758 1552 2 1 pm140_n1392 rfl
    (by decide) (by decide) (by decide) (by decide)

private theorem pm140_eval_1556 (initPM : Store) :
    denoteGraph pm initPM 1556 = chunkPrimDimN 1 pm.numRanks 3 (denoteGraph pm initPM 758) := by
  apply denote_chunkPrim_step pm initPM 1393 758 1556 3 1 pm140_n1393 rfl
    (by decide) (by decide) (by decide) (by decide)

private theorem sm140_init_597 (initSM : Store) : denoteGraph sm initSM 597 = initSM 597 :=
  denote_init_tid sm initSM 597 (by decide)

private theorem pm140_init_1557 (initPM : Store) : denoteGraph pm initPM 1557 = initPM 1557 :=
  denote_init_tid pm initPM 1557 (by decide)
private theorem pm140_init_1558 (initPM : Store) : denoteGraph pm initPM 1558 = initPM 1558 :=
  denote_init_tid pm initPM 1558 (by decide)
private theorem pm140_init_1559 (initPM : Store) : denoteGraph pm initPM 1559 = initPM 1559 :=
  denote_init_tid pm initPM 1559 (by decide)
private theorem pm140_init_1560 (initPM : Store) : denoteGraph pm initPM 1560 = initPM 1560 :=
  denote_init_tid pm initPM 1560 (by decide)


/-! ### Goal 175 — same structure as 140 (SM idx 180, PM BW_linear idx 1192..1195). -/

@[reducible] private def sm_n180 : NodeDecl :=
  { rank := 0, op := "OpName.BW_linear", ins := [802, 631, 632], outs := [800, 801] }
@[reducible] private def pm175_n1192 : NodeDecl :=
  { rank := 0, op := "OpName.BW_linear", ins := [2131, 631, 2113], outs := [2138, 2130] }
@[reducible] private def pm175_n1193 : NodeDecl :=
  { rank := 1, op := "OpName.BW_linear", ins := [2134, 631, 2114], outs := [2135, 2133] }
@[reducible] private def pm175_n1194 : NodeDecl :=
  { rank := 2, op := "OpName.BW_linear", ins := [2137, 631, 2115], outs := [2132, 2136] }
@[reducible] private def pm175_n1195 : NodeDecl :=
  { rank := 3, op := "OpName.BW_linear", ins := [2140, 631, 2116], outs := [2129, 2139] }
@[reducible] private def pm175_n1196 : NodeDecl :=
  { rank := 0, op := "OpName.AllReducePrim", ins := [2138, 2135, 2132, 2129], outs := [800] }
@[reducible] private def pm175_n1197 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [800], outs := [2100], params := [1] }
@[reducible] private def pm175_n1198 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [800], outs := [2104], params := [1] }
@[reducible] private def pm175_n1199 : NodeDecl :=
  { rank := 2, op := "OpName.ChunkPrim", ins := [800], outs := [2108], params := [1] }
@[reducible] private def pm175_n1200 : NodeDecl :=
  { rank := 3, op := "OpName.ChunkPrim", ins := [800], outs := [2112], params := [1] }

private theorem sm175_eval_800 (initSM : Store) :
    denoteGraph sm initSM 800 =
      (bw_linear (denoteGraph sm initSM 802) (denoteGraph sm initSM 631)
                 (denoteGraph sm initSM 632)).1 := by
  apply denote_bw_linear_fst_step sm initSM 180 802 631 632 800 801 0 sm_n180 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm175_eval_2138 (initPM : Store) :
    denoteGraph pm initPM 2138 =
      (bw_linear (denoteGraph pm initPM 2131) (denoteGraph pm initPM 631)
                 (denoteGraph pm initPM 2113)).1 := by
  apply denote_bw_linear_fst_step pm initPM 1192 2131 631 2113 2138 2130 0 pm175_n1192 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm175_eval_2135 (initPM : Store) :
    denoteGraph pm initPM 2135 =
      (bw_linear (denoteGraph pm initPM 2134) (denoteGraph pm initPM 631)
                 (denoteGraph pm initPM 2114)).1 := by
  apply denote_bw_linear_fst_step pm initPM 1193 2134 631 2114 2135 2133 1 pm175_n1193 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm175_eval_2132 (initPM : Store) :
    denoteGraph pm initPM 2132 =
      (bw_linear (denoteGraph pm initPM 2137) (denoteGraph pm initPM 631)
                 (denoteGraph pm initPM 2115)).1 := by
  apply denote_bw_linear_fst_step pm initPM 1194 2137 631 2115 2132 2136 2 pm175_n1194 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm175_eval_2129 (initPM : Store) :
    denoteGraph pm initPM 2129 =
      (bw_linear (denoteGraph pm initPM 2140) (denoteGraph pm initPM 631)
                 (denoteGraph pm initPM 2116)).1 := by
  apply denote_bw_linear_fst_step pm initPM 1195 2140 631 2116 2129 2139 3 pm175_n1195 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm175_eval_800 (initPM : Store) :
    denoteGraph pm initPM 800 = allReducePrim pm.numRanks 0
      ([2138, 2135, 2132, 2129].map (denoteGraph pm initPM)) := by
  apply denote_allReducePrim_step pm initPM 1196 [2138, 2135, 2132, 2129] 800 0 pm175_n1196 rfl
    (by decide) (by decide) (by decide)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl <;> decide

private theorem pm175_eval_2100 (initPM : Store) :
    denoteGraph pm initPM 2100 = chunkPrimDimN 1 pm.numRanks 0 (denoteGraph pm initPM 800) := by
  apply denote_chunkPrim_step pm initPM 1197 800 2100 0 1 pm175_n1197 rfl
    (by decide) (by decide) (by decide) (by decide)

private theorem pm175_eval_2104 (initPM : Store) :
    denoteGraph pm initPM 2104 = chunkPrimDimN 1 pm.numRanks 1 (denoteGraph pm initPM 800) := by
  apply denote_chunkPrim_step pm initPM 1198 800 2104 1 1 pm175_n1198 rfl
    (by decide) (by decide) (by decide) (by decide)

private theorem pm175_eval_2108 (initPM : Store) :
    denoteGraph pm initPM 2108 = chunkPrimDimN 1 pm.numRanks 2 (denoteGraph pm initPM 800) := by
  apply denote_chunkPrim_step pm initPM 1199 800 2108 2 1 pm175_n1199 rfl
    (by decide) (by decide) (by decide) (by decide)

private theorem pm175_eval_2112 (initPM : Store) :
    denoteGraph pm initPM 2112 = chunkPrimDimN 1 pm.numRanks 3 (denoteGraph pm initPM 800) := by
  apply denote_chunkPrim_step pm initPM 1200 800 2112 3 1 pm175_n1200 rfl
    (by decide) (by decide) (by decide) (by decide)

private theorem sm175_init_632 (initSM : Store) : denoteGraph sm initSM 632 = initSM 632 :=
  denote_init_tid sm initSM 632 (by decide)
private theorem pm175_init_2113 (initPM : Store) : denoteGraph pm initPM 2113 = initPM 2113 :=
  denote_init_tid pm initPM 2113 (by decide)
private theorem pm175_init_2114 (initPM : Store) : denoteGraph pm initPM 2114 = initPM 2114 :=
  denote_init_tid pm initPM 2114 (by decide)
private theorem pm175_init_2115 (initPM : Store) : denoteGraph pm initPM 2115 = initPM 2115 :=
  denote_init_tid pm initPM 2115 (by decide)
private theorem pm175_init_2116 (initPM : Store) : denoteGraph pm initPM 2116 = initPM 2116 :=
  denote_init_tid pm initPM 2116 (by decide)

/-! ### Goal 254 — same structure (SM idx 119, PM BW_linear idx 779,780,781,783). -/

@[reducible] private def sm_n119 : NodeDecl :=
  { rank := 0, op := "OpName.BW_linear", ins := [895, 710, 711], outs := [893, 894] }
@[reducible] private def pm254_n779 : NodeDecl :=
  { rank := 0, op := "OpName.BW_linear", ins := [3387, 710, 3369], outs := [3394, 3386] }
@[reducible] private def pm254_n780 : NodeDecl :=
  { rank := 1, op := "OpName.BW_linear", ins := [3390, 710, 3370], outs := [3391, 3389] }
@[reducible] private def pm254_n781 : NodeDecl :=
  { rank := 2, op := "OpName.BW_linear", ins := [3393, 710, 3371], outs := [3388, 3392] }
@[reducible] private def pm254_n783 : NodeDecl :=
  { rank := 3, op := "OpName.BW_linear", ins := [3396, 710, 3372], outs := [3385, 3395] }
@[reducible] private def pm254_n784 : NodeDecl :=
  { rank := 0, op := "OpName.AllReducePrim", ins := [3394, 3391, 3388, 3385], outs := [893] }
@[reducible] private def pm254_n785 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [893], outs := [3359], params := [1] }
@[reducible] private def pm254_n786 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [893], outs := [3362], params := [1] }
@[reducible] private def pm254_n787 : NodeDecl :=
  { rank := 2, op := "OpName.ChunkPrim", ins := [893], outs := [3365], params := [1] }
@[reducible] private def pm254_n788 : NodeDecl :=
  { rank := 3, op := "OpName.ChunkPrim", ins := [893], outs := [3368], params := [1] }

private theorem sm254_eval_893 (initSM : Store) :
    denoteGraph sm initSM 893 =
      (bw_linear (denoteGraph sm initSM 895) (denoteGraph sm initSM 710)
                 (denoteGraph sm initSM 711)).1 := by
  apply denote_bw_linear_fst_step sm initSM 119 895 710 711 893 894 0 sm_n119 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm254_eval_3394 (initPM : Store) :
    denoteGraph pm initPM 3394 =
      (bw_linear (denoteGraph pm initPM 3387) (denoteGraph pm initPM 710)
                 (denoteGraph pm initPM 3369)).1 := by
  apply denote_bw_linear_fst_step pm initPM 779 3387 710 3369 3394 3386 0 pm254_n779 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm254_eval_3391 (initPM : Store) :
    denoteGraph pm initPM 3391 =
      (bw_linear (denoteGraph pm initPM 3390) (denoteGraph pm initPM 710)
                 (denoteGraph pm initPM 3370)).1 := by
  apply denote_bw_linear_fst_step pm initPM 780 3390 710 3370 3391 3389 1 pm254_n780 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm254_eval_3388 (initPM : Store) :
    denoteGraph pm initPM 3388 =
      (bw_linear (denoteGraph pm initPM 3393) (denoteGraph pm initPM 710)
                 (denoteGraph pm initPM 3371)).1 := by
  apply denote_bw_linear_fst_step pm initPM 781 3393 710 3371 3388 3392 2 pm254_n781 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm254_eval_3385 (initPM : Store) :
    denoteGraph pm initPM 3385 =
      (bw_linear (denoteGraph pm initPM 3396) (denoteGraph pm initPM 710)
                 (denoteGraph pm initPM 3372)).1 := by
  apply denote_bw_linear_fst_step pm initPM 783 3396 710 3372 3385 3395 3 pm254_n783 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm254_eval_893 (initPM : Store) :
    denoteGraph pm initPM 893 = allReducePrim pm.numRanks 0
      ([3394, 3391, 3388, 3385].map (denoteGraph pm initPM)) := by
  apply denote_allReducePrim_step pm initPM 784 [3394, 3391, 3388, 3385] 893 0 pm254_n784 rfl
    (by decide) (by decide) (by decide)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl <;> decide

private theorem pm254_eval_3359 (initPM : Store) :
    denoteGraph pm initPM 3359 = chunkPrimDimN 1 pm.numRanks 0 (denoteGraph pm initPM 893) := by
  apply denote_chunkPrim_step pm initPM 785 893 3359 0 1 pm254_n785 rfl
    (by decide) (by decide) (by decide) (by decide)

private theorem pm254_eval_3362 (initPM : Store) :
    denoteGraph pm initPM 3362 = chunkPrimDimN 1 pm.numRanks 1 (denoteGraph pm initPM 893) := by
  apply denote_chunkPrim_step pm initPM 786 893 3362 1 1 pm254_n786 rfl
    (by decide) (by decide) (by decide) (by decide)

private theorem pm254_eval_3365 (initPM : Store) :
    denoteGraph pm initPM 3365 = chunkPrimDimN 1 pm.numRanks 2 (denoteGraph pm initPM 893) := by
  apply denote_chunkPrim_step pm initPM 787 893 3365 2 1 pm254_n787 rfl
    (by decide) (by decide) (by decide) (by decide)

private theorem pm254_eval_3368 (initPM : Store) :
    denoteGraph pm initPM 3368 = chunkPrimDimN 1 pm.numRanks 3 (denoteGraph pm initPM 893) := by
  apply denote_chunkPrim_step pm initPM 788 893 3368 3 1 pm254_n788 rfl
    (by decide) (by decide) (by decide) (by decide)

private theorem sm254_init_711 (initSM : Store) : denoteGraph sm initSM 711 = initSM 711 :=
  denote_init_tid sm initSM 711 (by decide)
private theorem pm254_init_3369 (initPM : Store) : denoteGraph pm initPM 3369 = initPM 3369 :=
  denote_init_tid pm initPM 3369 (by decide)
private theorem pm254_init_3370 (initPM : Store) : denoteGraph pm initPM 3370 = initPM 3370 :=
  denote_init_tid pm initPM 3370 (by decide)
private theorem pm254_init_3371 (initPM : Store) : denoteGraph pm initPM 3371 = initPM 3371 :=
  denote_init_tid pm initPM 3371 (by decide)
private theorem pm254_init_3372 (initPM : Store) : denoteGraph pm initPM 3372 = initPM 3372 :=
  denote_init_tid pm initPM 3372 (by decide)


/-! ## Goal proofs.

NOTE (RELAY P78 v8): The helper lemmas and per-tid evaluation theorems above
are fully proven. However, `prove_goal_140` / `prove_goal_175` / `prove_goal_254`
require the bridge `bw_linear_3d_fst_row_parallel` whose elaboration in this
context triggers a `whnf` blow-up exceeding even 400M heartbeats. Left as
sorry pending further investigation (see RELAY_78_v8_REPORT.md). -/

private theorem prove_goal_140 : goal_140_stmt := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- gradOut prereq (goal_142 ↦ Pattern_79)
  have h142 := prove_pattern_79 (target := goal_142_stmt) pattern_79_target.goal_142
    initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h142_SH, hgr_sh, h142_REC⟩ := h142
  simp only [goal_142, List.map_cons, List.map_nil] at hgr_sh h142_REC
  have hgr0_sh : (denoteGraph pm initPM 1575).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.1
  have hgr1_sh : (denoteGraph pm initPM 1578).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.1
  have hgr2_sh : (denoteGraph pm initPM 1581).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.2.1
  have hgr3_sh : (denoteGraph pm initPM 1584).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  have h142_DIMN : denoteGraph sm initSM 760 = allGatherPrimDimN 2 pm.numRanks 0
      [denoteGraph pm initPM 1575, denoteGraph pm initPM 1578,
       denoteGraph pm initPM 1581, denoteGraph pm initPM 1584] := by
    rw [h142_REC]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hgr0_sh]; intro hc; cases hc
  -- x prereq (goal_25 ↦ Pattern_21, singleton)
  have h25 := prove_pattern_21 (target := goal_25_stmt) pattern_21_target.goal_25
    initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h25_SH, _, h25_REC⟩ := h25
  simp only [goal_25, List.map_cons, List.map_nil, reconstructWithDim_singleton] at h25_REC
  have h25_SH' : (denoteGraph sm initSM 596).shape = [1, 8, 32] := by
    have := h25_SH; simp only [goal_25] at this; exact this
  -- weight initGoal_597
  have h597_init := hInitGoals initGoal_597 (by simp [initGoals])
  obtain ⟨h597_sh, hw_sh, h597_rec⟩ := h597_init
  simp only [initGoal_597, List.map_cons, List.map_nil] at h597_rec hw_sh
  have hwr0_sh : (initPM 1557).shape = [32, 32] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.1
  have h597_dimN : initSM 597 = allGatherPrimDimN 0 pm.numRanks 0
      [initPM 1557, initPM 1558, initPM 1559, initPM 1560] := by
    rw [h597_rec]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hwr0_sh]; intro hc; cases hc
  -- Lift 597 / 1557-1560 from init store to denoteGraph.
  have H597 := sm140_init_597 initSM
  have H1557 := pm140_init_1557 initPM
  have H1558 := pm140_init_1558 initPM
  have H1559 := pm140_init_1559 initPM
  have H1560 := pm140_init_1560 initPM
  -- sm / pm dX evaluations
  have hS := sm140_eval_758 initSM
  have hP0 := pm140_eval_1582 initPM
  have hP1 := pm140_eval_1579 initPM
  have hP2 := pm140_eval_1576 initPM
  have hP3 := pm140_eval_1573 initPM
  have hPar := pm140_eval_758 initPM
  -- per-shard shapes / final result shape
  have h597_sh' : (denoteGraph sm initSM 597).shape = [128, 32] := by
    rw [H597]
    have := h597_sh; simp only [initGoal_597] at this; exact this
  have hwr0_pm_sh : (denoteGraph pm initPM 1557).shape = [32, 32] := by
    rw [H1557]; exact hwr0_sh
  have hwr1_pm_sh : (denoteGraph pm initPM 1558).shape = [32, 32] := by
    rw [H1558]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.1
  have hwr2_pm_sh : (denoteGraph pm initPM 1559).shape = [32, 32] := by
    rw [H1559]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.1
  have hwr3_pm_sh : (denoteGraph pm initPM 1560).shape = [32, 32] := by
    rw [H1560]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  have h25_PM_SH : (denoteGraph pm initPM 596).shape = [1, 8, 32] := by
    rw [← h25_REC]; exact h25_SH'
  -- 760 (full gradOut) shape
  have h142_SH' : (denoteGraph sm initSM 760).shape = [1, 8, 128] := by
    have := h142_SH; simp only [goal_142] at this; exact this
  -- LHS: sm 758 shape = [1, 8, 32]
  have hLHS_sh : (denoteGraph sm initSM 758).shape = [1, 8, 32] := by
    rw [hS]
    exact bw_linear_3d_fst_shape 1 8 128 32 _ _ _ h142_SH' h25_SH' h597_sh'
  -- bridge_dX_4 application: full_o = shard_o * 4 = 32 * 4 = 128, but we shape it [128, 32]
  -- Build the bridge equality
  have hbridge := bridge_dX_4 1 8 32 32
      (denoteGraph pm initPM 1575) (denoteGraph pm initPM 1578)
      (denoteGraph pm initPM 1581) (denoteGraph pm initPM 1584)
      (denoteGraph pm initPM 596)
      (denoteGraph pm initPM 1557) (denoteGraph pm initPM 1558)
      (denoteGraph pm initPM 1559) (denoteGraph pm initPM 1560)
      hgr0_sh hgr1_sh hgr2_sh hgr3_sh
      hwr0_pm_sh hwr1_pm_sh hwr2_pm_sh hwr3_pm_sh
      h25_PM_SH
      (by decide) (by decide)
  -- pm dx shard shapes
  have hP0_sh : (denoteGraph pm initPM 1582).shape = [1, 8, 32] := by
    rw [hP0]
    exact bw_linear_3d_fst_shape 1 8 32 32 _ _ _ hgr0_sh h25_PM_SH hwr0_pm_sh
  have hP1_sh : (denoteGraph pm initPM 1579).shape = [1, 8, 32] := by
    rw [hP1]
    exact bw_linear_3d_fst_shape 1 8 32 32 _ _ _ hgr1_sh h25_PM_SH hwr1_pm_sh
  have hP2_sh : (denoteGraph pm initPM 1576).shape = [1, 8, 32] := by
    rw [hP2]
    exact bw_linear_3d_fst_shape 1 8 32 32 _ _ _ hgr2_sh h25_PM_SH hwr2_pm_sh
  have hP3_sh : (denoteGraph pm initPM 1573).shape = [1, 8, 32] := by
    rw [hP3]
    exact bw_linear_3d_fst_shape 1 8 32 32 _ _ _ hgr3_sh h25_PM_SH hwr3_pm_sh
  have hnr : pm.numRanks = 4 := rfl
  -- Rewrite h142_DIMN, h597_dimN with hnr
  have h142_DIMN4 : denoteGraph sm initSM 760 = allGatherPrimDimN 2 4 0
      [denoteGraph pm initPM 1575, denoteGraph pm initPM 1578,
       denoteGraph pm initPM 1581, denoteGraph pm initPM 1584] := by
    rw [h142_DIMN, hnr]
  have h597_dimN4 : denoteGraph sm initSM 597 = allGatherPrimDimN 0 4 0
      [denoteGraph pm initPM 1557, denoteGraph pm initPM 1558,
       denoteGraph pm initPM 1559, denoteGraph pm initPM 1560] := by
    rw [H597, h597_dimN, hnr, H1557, H1558, H1559, H1560]
  -- sm 758 = pm 758 via bridge + parallel evaluator
  have h758_eq : denoteGraph sm initSM 758 = denoteGraph pm initPM 758 := by
    rw [hS, h142_DIMN4, h25_REC, h597_dimN4, hbridge, hPar, hnr]
    simp only [List.map_cons, List.map_nil]
    rw [← hP0, ← hP1, ← hP2, ← hP3]
  -- pm 758 shape (transfer from LHS shape)
  have h758_pm_sh : (denoteGraph pm initPM 758).shape = [1, 8, 32] := by
    rw [← h758_eq]; exact hLHS_sh
  -- chunk pieces shapes/values
  have hC0 := pm140_eval_1544 initPM
  have hC1 := pm140_eval_1548 initPM
  have hC2 := pm140_eval_1552 initPM
  have hC3 := pm140_eval_1556 initPM
  have hC0_sh : (denoteGraph pm initPM 1544).shape = [1, 2, 32] := by
    rw [hC0, hnr]
    exact chunkPrimDimN_1_4_shape _ 32 0 h758_pm_sh
  have hC1_sh : (denoteGraph pm initPM 1548).shape = [1, 2, 32] := by
    rw [hC1, hnr]
    exact chunkPrimDimN_1_4_shape _ 32 1 h758_pm_sh
  have hC2_sh : (denoteGraph pm initPM 1552).shape = [1, 2, 32] := by
    rw [hC2, hnr]
    exact chunkPrimDimN_1_4_shape _ 32 2 h758_pm_sh
  have hC3_sh : (denoteGraph pm initPM 1556).shape = [1, 2, 32] := by
    rw [hC3, hnr]
    exact chunkPrimDimN_1_4_shape _ 32 3 h758_pm_sh
  -- Reconstruction: sm 758 = allGatherPrimDimN 1 4 0 [chunks of pm 758]
  --                       = pm 758 = sm 758
  refine ⟨?_, ?_, ?_⟩
  · show (denoteGraph sm initSM 758).shape = [1, 8, 32]; exact hLHS_sh
  · show List.map (fun t => Tensor.shape t)
        ([({ rank := 0, tid := 1544 } : Piece),
          ({ rank := 1, tid := 1548 } : Piece),
          ({ rank := 2, tid := 1552 } : Piece),
          ({ rank := 3, tid := 1556 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]]
    simp only [List.map_cons, List.map_nil]
    rw [hC0_sh, hC1_sh, hC2_sh, hC3_sh]
  · show denoteGraph sm initSM 758 =
        reconstructWithDim 1 pm.numRanks 0
          ([({ rank := 0, tid := 1544 } : Piece),
            ({ rank := 1, tid := 1548 } : Piece),
            ({ rank := 2, tid := 1552 } : Piece),
            ({ rank := 3, tid := 1556 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
    simp only [List.map_cons, List.map_nil]
    rw [hnr]
    rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _
      (by rw [hC0_sh]; intro hc; cases hc)]
    rw [hC0, hC1, hC2, hC3, hnr]
    rw [h758_eq]
    exact (gather_chunk_dim1_1_8_32 _ h758_pm_sh).symm
private theorem prove_goal_175 : goal_175_stmt := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  have h177 := prove_pattern_98 (target := goal_177_stmt) pattern_98_target.goal_177
    initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h177_SH, hgr_sh, h177_REC⟩ := h177
  simp only [goal_177, List.map_cons, List.map_nil] at hgr_sh h177_REC
  have hgr0_sh : (denoteGraph pm initPM 2131).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.1
  have hgr1_sh : (denoteGraph pm initPM 2134).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.1
  have hgr2_sh : (denoteGraph pm initPM 2137).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.2.1
  have hgr3_sh : (denoteGraph pm initPM 2140).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  have h177_DIMN : denoteGraph sm initSM 802 = allGatherPrimDimN 2 pm.numRanks 0
      [denoteGraph pm initPM 2131, denoteGraph pm initPM 2134,
       denoteGraph pm initPM 2137, denoteGraph pm initPM 2140] := by
    rw [h177_REC]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hgr0_sh]; intro hc; cases hc
  have h50 := prove_pattern_21 (target := goal_50_stmt) pattern_21_target.goal_50
    initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h50_SH, _, h50_REC⟩ := h50
  simp only [goal_50, List.map_cons, List.map_nil, reconstructWithDim_singleton] at h50_REC
  have h50_SH' : (denoteGraph sm initSM 631).shape = [1, 8, 32] := by
    have := h50_SH; simp only [goal_50] at this; exact this
  have h632_init := hInitGoals initGoal_632 (by simp [initGoals])
  obtain ⟨h632_sh, hw_sh, h632_rec⟩ := h632_init
  simp only [initGoal_632, List.map_cons, List.map_nil] at h632_rec hw_sh
  have hwr0_sh : (initPM 2113).shape = [32, 32] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.1
  have h632_dimN : initSM 632 = allGatherPrimDimN 0 pm.numRanks 0
      [initPM 2113, initPM 2114, initPM 2115, initPM 2116] := by
    rw [h632_rec]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hwr0_sh]; intro hc; cases hc
  have H632 := sm175_init_632 initSM
  have H2113 := pm175_init_2113 initPM
  have H2114 := pm175_init_2114 initPM
  have H2115 := pm175_init_2115 initPM
  have H2116 := pm175_init_2116 initPM
  have hS := sm175_eval_800 initSM
  have hP0 := pm175_eval_2138 initPM
  have hP1 := pm175_eval_2135 initPM
  have hP2 := pm175_eval_2132 initPM
  have hP3 := pm175_eval_2129 initPM
  have hPar := pm175_eval_800 initPM
  have h632_sh' : (denoteGraph sm initSM 632).shape = [128, 32] := by
    rw [H632]; have := h632_sh; simp only [initGoal_632] at this; exact this
  have hwr0_pm_sh : (denoteGraph pm initPM 2113).shape = [32, 32] := by
    rw [H2113]; exact hwr0_sh
  have hwr1_pm_sh : (denoteGraph pm initPM 2114).shape = [32, 32] := by
    rw [H2114]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.1
  have hwr2_pm_sh : (denoteGraph pm initPM 2115).shape = [32, 32] := by
    rw [H2115]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.1
  have hwr3_pm_sh : (denoteGraph pm initPM 2116).shape = [32, 32] := by
    rw [H2116]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  have h50_PM_SH : (denoteGraph pm initPM 631).shape = [1, 8, 32] := by
    rw [← h50_REC]; exact h50_SH'
  have h177_SH' : (denoteGraph sm initSM 802).shape = [1, 8, 128] := by
    have := h177_SH; simp only [goal_177] at this; exact this
  have hLHS_sh : (denoteGraph sm initSM 800).shape = [1, 8, 32] := by
    rw [hS]
    exact bw_linear_3d_fst_shape 1 8 128 32 _ _ _ h177_SH' h50_SH' h632_sh'
  have hbridge := bridge_dX_4 1 8 32 32
      (denoteGraph pm initPM 2131) (denoteGraph pm initPM 2134)
      (denoteGraph pm initPM 2137) (denoteGraph pm initPM 2140)
      (denoteGraph pm initPM 631)
      (denoteGraph pm initPM 2113) (denoteGraph pm initPM 2114)
      (denoteGraph pm initPM 2115) (denoteGraph pm initPM 2116)
      hgr0_sh hgr1_sh hgr2_sh hgr3_sh
      hwr0_pm_sh hwr1_pm_sh hwr2_pm_sh hwr3_pm_sh
      h50_PM_SH (by decide) (by decide)
  have hP0_sh : (denoteGraph pm initPM 2138).shape = [1, 8, 32] := by
    rw [hP0]
    exact bw_linear_3d_fst_shape 1 8 32 32 _ _ _ hgr0_sh h50_PM_SH hwr0_pm_sh
  have hP1_sh : (denoteGraph pm initPM 2135).shape = [1, 8, 32] := by
    rw [hP1]
    exact bw_linear_3d_fst_shape 1 8 32 32 _ _ _ hgr1_sh h50_PM_SH hwr1_pm_sh
  have hP2_sh : (denoteGraph pm initPM 2132).shape = [1, 8, 32] := by
    rw [hP2]
    exact bw_linear_3d_fst_shape 1 8 32 32 _ _ _ hgr2_sh h50_PM_SH hwr2_pm_sh
  have hP3_sh : (denoteGraph pm initPM 2129).shape = [1, 8, 32] := by
    rw [hP3]
    exact bw_linear_3d_fst_shape 1 8 32 32 _ _ _ hgr3_sh h50_PM_SH hwr3_pm_sh
  have hnr : pm.numRanks = 4 := rfl
  have h177_DIMN4 : denoteGraph sm initSM 802 = allGatherPrimDimN 2 4 0
      [denoteGraph pm initPM 2131, denoteGraph pm initPM 2134,
       denoteGraph pm initPM 2137, denoteGraph pm initPM 2140] := by
    rw [h177_DIMN, hnr]
  have h632_dimN4 : denoteGraph sm initSM 632 = allGatherPrimDimN 0 4 0
      [denoteGraph pm initPM 2113, denoteGraph pm initPM 2114,
       denoteGraph pm initPM 2115, denoteGraph pm initPM 2116] := by
    rw [H632, h632_dimN, hnr, H2113, H2114, H2115, H2116]
  have h800_eq : denoteGraph sm initSM 800 = denoteGraph pm initPM 800 := by
    rw [hS, h177_DIMN4, h50_REC, h632_dimN4, hbridge, hPar, hnr]
    simp only [List.map_cons, List.map_nil]
    rw [← hP0, ← hP1, ← hP2, ← hP3]
  have h800_pm_sh : (denoteGraph pm initPM 800).shape = [1, 8, 32] := by
    rw [← h800_eq]; exact hLHS_sh
  have hC0 := pm175_eval_2100 initPM
  have hC1 := pm175_eval_2104 initPM
  have hC2 := pm175_eval_2108 initPM
  have hC3 := pm175_eval_2112 initPM
  have hC0_sh : (denoteGraph pm initPM 2100).shape = [1, 2, 32] := by
    rw [hC0, hnr]; exact chunkPrimDimN_1_4_shape _ 32 0 h800_pm_sh
  have hC1_sh : (denoteGraph pm initPM 2104).shape = [1, 2, 32] := by
    rw [hC1, hnr]; exact chunkPrimDimN_1_4_shape _ 32 1 h800_pm_sh
  have hC2_sh : (denoteGraph pm initPM 2108).shape = [1, 2, 32] := by
    rw [hC2, hnr]; exact chunkPrimDimN_1_4_shape _ 32 2 h800_pm_sh
  have hC3_sh : (denoteGraph pm initPM 2112).shape = [1, 2, 32] := by
    rw [hC3, hnr]; exact chunkPrimDimN_1_4_shape _ 32 3 h800_pm_sh
  refine ⟨?_, ?_, ?_⟩
  · show (denoteGraph sm initSM 800).shape = [1, 8, 32]; exact hLHS_sh
  · show List.map (fun t => Tensor.shape t)
        ([({ rank := 0, tid := 2100 } : Piece),
          ({ rank := 1, tid := 2104 } : Piece),
          ({ rank := 2, tid := 2108 } : Piece),
          ({ rank := 3, tid := 2112 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]]
    simp only [List.map_cons, List.map_nil]
    rw [hC0_sh, hC1_sh, hC2_sh, hC3_sh]
  · show denoteGraph sm initSM 800 =
        reconstructWithDim 1 pm.numRanks 0
          ([({ rank := 0, tid := 2100 } : Piece),
            ({ rank := 1, tid := 2104 } : Piece),
            ({ rank := 2, tid := 2108 } : Piece),
            ({ rank := 3, tid := 2112 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
    simp only [List.map_cons, List.map_nil]
    rw [hnr]
    rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _
      (by rw [hC0_sh]; intro hc; cases hc)]
    rw [hC0, hC1, hC2, hC3, hnr]
    rw [h800_eq]
    exact (gather_chunk_dim1_1_8_32 _ h800_pm_sh).symm


/-! ### Goal 178 — `bw_linear` row-parallel dx (iX = 128).

  SM tid 803 = `(bw_linear gradOut x w).1` with gradOut=805, x=634, w=635.
  SM node `outs := [803, 804]` is at SM index 178.
  PM BW_linear at indices 1175..1178, AR at 1179, Chunks at 1180..1183.
-/

@[reducible] private def sm_n178 : NodeDecl :=
  { rank := 0, op := "OpName.BW_linear", ins := [805, 634, 635], outs := [803, 804] }

@[reducible] private def pm178_n1175 : NodeDecl :=
  { rank := 0, op := "OpName.BW_linear", ins := [2183, 634, 2165], outs := [2190, 2182] }
@[reducible] private def pm178_n1176 : NodeDecl :=
  { rank := 1, op := "OpName.BW_linear", ins := [2186, 634, 2166], outs := [2187, 2185] }
@[reducible] private def pm178_n1177 : NodeDecl :=
  { rank := 2, op := "OpName.BW_linear", ins := [2189, 634, 2167], outs := [2184, 2188] }
@[reducible] private def pm178_n1178 : NodeDecl :=
  { rank := 3, op := "OpName.BW_linear", ins := [2192, 634, 2168], outs := [2181, 2191] }
@[reducible] private def pm178_n1179 : NodeDecl :=
  { rank := 0, op := "OpName.AllReducePrim", ins := [2190, 2187, 2184, 2181], outs := [803] }
@[reducible] private def pm178_n1180 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [803], outs := [2158], params := [1] }
@[reducible] private def pm178_n1181 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [803], outs := [2160], params := [1] }
@[reducible] private def pm178_n1182 : NodeDecl :=
  { rank := 2, op := "OpName.ChunkPrim", ins := [803], outs := [2162], params := [1] }
@[reducible] private def pm178_n1183 : NodeDecl :=
  { rank := 3, op := "OpName.ChunkPrim", ins := [803], outs := [2164], params := [1] }

private theorem sm178_eval_803 (initSM : Store) :
    denoteGraph sm initSM 803 =
      (bw_linear (denoteGraph sm initSM 805) (denoteGraph sm initSM 634)
                 (denoteGraph sm initSM 635)).1 := by
  apply denote_bw_linear_fst_step sm initSM 178 805 634 635 803 804 0 sm_n178 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm178_eval_2190 (initPM : Store) :
    denoteGraph pm initPM 2190 =
      (bw_linear (denoteGraph pm initPM 2183) (denoteGraph pm initPM 634)
                 (denoteGraph pm initPM 2165)).1 := by
  apply denote_bw_linear_fst_step pm initPM 1175 2183 634 2165 2190 2182 0 pm178_n1175 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm178_eval_2187 (initPM : Store) :
    denoteGraph pm initPM 2187 =
      (bw_linear (denoteGraph pm initPM 2186) (denoteGraph pm initPM 634)
                 (denoteGraph pm initPM 2166)).1 := by
  apply denote_bw_linear_fst_step pm initPM 1176 2186 634 2166 2187 2185 1 pm178_n1176 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm178_eval_2184 (initPM : Store) :
    denoteGraph pm initPM 2184 =
      (bw_linear (denoteGraph pm initPM 2189) (denoteGraph pm initPM 634)
                 (denoteGraph pm initPM 2167)).1 := by
  apply denote_bw_linear_fst_step pm initPM 1177 2189 634 2167 2184 2188 2 pm178_n1177 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm178_eval_2181 (initPM : Store) :
    denoteGraph pm initPM 2181 =
      (bw_linear (denoteGraph pm initPM 2192) (denoteGraph pm initPM 634)
                 (denoteGraph pm initPM 2168)).1 := by
  apply denote_bw_linear_fst_step pm initPM 1178 2192 634 2168 2181 2191 3 pm178_n1178 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm178_eval_803 (initPM : Store) :
    denoteGraph pm initPM 803 = allReducePrim pm.numRanks 0
      ([2190, 2187, 2184, 2181].map (denoteGraph pm initPM)) := by
  apply denote_allReducePrim_step pm initPM 1179 [2190, 2187, 2184, 2181] 803 0 pm178_n1179 rfl
    (by decide) (by decide) (by decide)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl <;> decide

private theorem pm178_eval_2158 (initPM : Store) :
    denoteGraph pm initPM 2158 = chunkPrimDimN 1 pm.numRanks 0 (denoteGraph pm initPM 803) := by
  apply denote_chunkPrim_step pm initPM 1180 803 2158 0 1 pm178_n1180 rfl
    (by decide) (by decide) (by decide) (by decide)

private theorem pm178_eval_2160 (initPM : Store) :
    denoteGraph pm initPM 2160 = chunkPrimDimN 1 pm.numRanks 1 (denoteGraph pm initPM 803) := by
  apply denote_chunkPrim_step pm initPM 1181 803 2160 1 1 pm178_n1181 rfl
    (by decide) (by decide) (by decide) (by decide)

private theorem pm178_eval_2162 (initPM : Store) :
    denoteGraph pm initPM 2162 = chunkPrimDimN 1 pm.numRanks 2 (denoteGraph pm initPM 803) := by
  apply denote_chunkPrim_step pm initPM 1182 803 2162 2 1 pm178_n1182 rfl
    (by decide) (by decide) (by decide) (by decide)

private theorem pm178_eval_2164 (initPM : Store) :
    denoteGraph pm initPM 2164 = chunkPrimDimN 1 pm.numRanks 3 (denoteGraph pm initPM 803) := by
  apply denote_chunkPrim_step pm initPM 1183 803 2164 3 1 pm178_n1183 rfl
    (by decide) (by decide) (by decide) (by decide)

private theorem sm178_init_635 (initSM : Store) : denoteGraph sm initSM 635 = initSM 635 :=
  denote_init_tid sm initSM 635 (by decide)
private theorem pm178_init_2165 (initPM : Store) : denoteGraph pm initPM 2165 = initPM 2165 :=
  denote_init_tid pm initPM 2165 (by decide)
private theorem pm178_init_2166 (initPM : Store) : denoteGraph pm initPM 2166 = initPM 2166 :=
  denote_init_tid pm initPM 2166 (by decide)
private theorem pm178_init_2167 (initPM : Store) : denoteGraph pm initPM 2167 = initPM 2167 :=
  denote_init_tid pm initPM 2167 (by decide)
private theorem pm178_init_2168 (initPM : Store) : denoteGraph pm initPM 2168 = initPM 2168 :=
  denote_init_tid pm initPM 2168 (by decide)

private theorem prove_goal_178 : goal_178_stmt := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- gradOut prereq (goal_180 ↦ Pattern_99), shards [1,8,8] gather dim 2 → [1,8,32]
  have h180 := prove_pattern_99 (target := goal_180_stmt) pattern_99_target.goal_180
    initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h180_SH, hgr_sh, h180_REC⟩ := h180
  simp only [goal_180, List.map_cons, List.map_nil] at hgr_sh h180_REC
  have hgr0_sh : (denoteGraph pm initPM 2183).shape = [1, 8, 8] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.1
  have hgr1_sh : (denoteGraph pm initPM 2186).shape = [1, 8, 8] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.1
  have hgr2_sh : (denoteGraph pm initPM 2189).shape = [1, 8, 8] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.2.1
  have hgr3_sh : (denoteGraph pm initPM 2192).shape = [1, 8, 8] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  have h180_DIMN : denoteGraph sm initSM 805 = allGatherPrimDimN 2 pm.numRanks 0
      [denoteGraph pm initPM 2183, denoteGraph pm initPM 2186,
       denoteGraph pm initPM 2189, denoteGraph pm initPM 2192] := by
    rw [h180_REC]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hgr0_sh]; intro hc; cases hc
  -- x prereq (goal_52 ↦ Pattern_35, singleton)
  have h52 := prove_pattern_35 (target := goal_52_stmt) pattern_35_target.goal_52
    initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h52_SH, _, h52_REC⟩ := h52
  simp only [goal_52, List.map_cons, List.map_nil, reconstructWithDim_singleton] at h52_REC
  have h52_SH' : (denoteGraph sm initSM 634).shape = [1, 8, 128] := by
    have := h52_SH; simp only [goal_52] at this; exact this
  -- weight initGoal_635
  have h635_init := hInitGoals initGoal_635 (by simp [initGoals])
  obtain ⟨h635_sh, hw_sh, h635_rec⟩ := h635_init
  simp only [initGoal_635, List.map_cons, List.map_nil] at h635_rec hw_sh
  have hwr0_sh : (initPM 2165).shape = [8, 128] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.1
  have h635_dimN : initSM 635 = allGatherPrimDimN 0 pm.numRanks 0
      [initPM 2165, initPM 2166, initPM 2167, initPM 2168] := by
    rw [h635_rec]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hwr0_sh]; intro hc; cases hc
  have H635 := sm178_init_635 initSM
  have H2165 := pm178_init_2165 initPM
  have H2166 := pm178_init_2166 initPM
  have H2167 := pm178_init_2167 initPM
  have H2168 := pm178_init_2168 initPM
  have hS := sm178_eval_803 initSM
  have hP0 := pm178_eval_2190 initPM
  have hP1 := pm178_eval_2187 initPM
  have hP2 := pm178_eval_2184 initPM
  have hP3 := pm178_eval_2181 initPM
  have hPar := pm178_eval_803 initPM
  have h635_sh' : (denoteGraph sm initSM 635).shape = [32, 128] := by
    rw [H635]
    have := h635_sh; simp only [initGoal_635] at this; exact this
  have hwr0_pm_sh : (denoteGraph pm initPM 2165).shape = [8, 128] := by
    rw [H2165]; exact hwr0_sh
  have hwr1_pm_sh : (denoteGraph pm initPM 2166).shape = [8, 128] := by
    rw [H2166]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.1
  have hwr2_pm_sh : (denoteGraph pm initPM 2167).shape = [8, 128] := by
    rw [H2167]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.1
  have hwr3_pm_sh : (denoteGraph pm initPM 2168).shape = [8, 128] := by
    rw [H2168]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  have h52_PM_SH : (denoteGraph pm initPM 634).shape = [1, 8, 128] := by
    rw [← h52_REC]; exact h52_SH'
  have h180_SH' : (denoteGraph sm initSM 805).shape = [1, 8, 32] := by
    have := h180_SH; simp only [goal_180] at this; exact this
  -- LHS: sm 803 shape = [1, 8, 128]
  have hLHS_sh : (denoteGraph sm initSM 803).shape = [1, 8, 128] := by
    rw [hS]
    exact bw_linear_3d_fst_shape 1 8 32 128 _ _ _ h180_SH' h52_SH' h635_sh'
  -- bridge_dX_4 with shard_o = 8, iX = 128
  have hbridge := bridge_dX_4 1 8 8 128
      (denoteGraph pm initPM 2183) (denoteGraph pm initPM 2186)
      (denoteGraph pm initPM 2189) (denoteGraph pm initPM 2192)
      (denoteGraph pm initPM 634)
      (denoteGraph pm initPM 2165) (denoteGraph pm initPM 2166)
      (denoteGraph pm initPM 2167) (denoteGraph pm initPM 2168)
      hgr0_sh hgr1_sh hgr2_sh hgr3_sh
      hwr0_pm_sh hwr1_pm_sh hwr2_pm_sh hwr3_pm_sh
      h52_PM_SH
      (by decide) (by decide)
  have hP0_sh : (denoteGraph pm initPM 2190).shape = [1, 8, 128] := by
    rw [hP0]
    exact bw_linear_3d_fst_shape 1 8 8 128 _ _ _ hgr0_sh h52_PM_SH hwr0_pm_sh
  have hP1_sh : (denoteGraph pm initPM 2187).shape = [1, 8, 128] := by
    rw [hP1]
    exact bw_linear_3d_fst_shape 1 8 8 128 _ _ _ hgr1_sh h52_PM_SH hwr1_pm_sh
  have hP2_sh : (denoteGraph pm initPM 2184).shape = [1, 8, 128] := by
    rw [hP2]
    exact bw_linear_3d_fst_shape 1 8 8 128 _ _ _ hgr2_sh h52_PM_SH hwr2_pm_sh
  have hP3_sh : (denoteGraph pm initPM 2181).shape = [1, 8, 128] := by
    rw [hP3]
    exact bw_linear_3d_fst_shape 1 8 8 128 _ _ _ hgr3_sh h52_PM_SH hwr3_pm_sh
  have hnr : pm.numRanks = 4 := rfl
  have h180_DIMN4 : denoteGraph sm initSM 805 = allGatherPrimDimN 2 4 0
      [denoteGraph pm initPM 2183, denoteGraph pm initPM 2186,
       denoteGraph pm initPM 2189, denoteGraph pm initPM 2192] := by
    rw [h180_DIMN, hnr]
  have h635_dimN4 : denoteGraph sm initSM 635 = allGatherPrimDimN 0 4 0
      [denoteGraph pm initPM 2165, denoteGraph pm initPM 2166,
       denoteGraph pm initPM 2167, denoteGraph pm initPM 2168] := by
    rw [H635, h635_dimN, hnr, H2165, H2166, H2167, H2168]
  have h803_eq : denoteGraph sm initSM 803 = denoteGraph pm initPM 803 := by
    rw [hS, h180_DIMN4, h52_REC, h635_dimN4, hbridge, hPar, hnr]
    simp only [List.map_cons, List.map_nil]
    rw [← hP0, ← hP1, ← hP2, ← hP3]
  have h803_pm_sh : (denoteGraph pm initPM 803).shape = [1, 8, 128] := by
    rw [← h803_eq]; exact hLHS_sh
  have hC0 := pm178_eval_2158 initPM
  have hC1 := pm178_eval_2160 initPM
  have hC2 := pm178_eval_2162 initPM
  have hC3 := pm178_eval_2164 initPM
  have hC0_sh : (denoteGraph pm initPM 2158).shape = [1, 2, 128] := by
    rw [hC0, hnr]; exact chunkPrimDimN_1_4_shape _ 128 0 h803_pm_sh
  have hC1_sh : (denoteGraph pm initPM 2160).shape = [1, 2, 128] := by
    rw [hC1, hnr]; exact chunkPrimDimN_1_4_shape _ 128 1 h803_pm_sh
  have hC2_sh : (denoteGraph pm initPM 2162).shape = [1, 2, 128] := by
    rw [hC2, hnr]; exact chunkPrimDimN_1_4_shape _ 128 2 h803_pm_sh
  have hC3_sh : (denoteGraph pm initPM 2164).shape = [1, 2, 128] := by
    rw [hC3, hnr]; exact chunkPrimDimN_1_4_shape _ 128 3 h803_pm_sh
  refine ⟨?_, ?_, ?_⟩
  · show (denoteGraph sm initSM 803).shape = [1, 8, 128]; exact hLHS_sh
  · show List.map (fun t => Tensor.shape t)
        ([({ rank := 0, tid := 2158 } : Piece),
          ({ rank := 1, tid := 2160 } : Piece),
          ({ rank := 2, tid := 2162 } : Piece),
          ({ rank := 3, tid := 2164 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) =
        [[1, 2, 128], [1, 2, 128], [1, 2, 128], [1, 2, 128]]
    simp only [List.map_cons, List.map_nil]
    rw [hC0_sh, hC1_sh, hC2_sh, hC3_sh]
  · show denoteGraph sm initSM 803 =
        reconstructWithDim 1 pm.numRanks 0
          ([({ rank := 0, tid := 2158 } : Piece),
            ({ rank := 1, tid := 2160 } : Piece),
            ({ rank := 2, tid := 2162 } : Piece),
            ({ rank := 3, tid := 2164 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
    simp only [List.map_cons, List.map_nil]
    rw [hnr]
    rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _
      (by rw [hC0_sh]; intro hc; cases hc)]
    rw [hC0, hC1, hC2, hC3, hnr]
    rw [h803_eq]
    exact (gather_chunk_dim1_1_8_128 _ h803_pm_sh).symm


private theorem prove_goal_254 : goal_254_stmt := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  have h256 := prove_pattern_126 (target := goal_256_stmt) pattern_126_target.goal_256
    initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h256_SH, hgr_sh, h256_REC⟩ := h256
  simp only [goal_256, List.map_cons, List.map_nil] at hgr_sh h256_REC
  have hgr0_sh : (denoteGraph pm initPM 3387).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.1
  have hgr1_sh : (denoteGraph pm initPM 3390).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.1
  have hgr2_sh : (denoteGraph pm initPM 3393).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.2.1
  have hgr3_sh : (denoteGraph pm initPM 3396).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  have h256_DIMN : denoteGraph sm initSM 895 = allGatherPrimDimN 2 pm.numRanks 0
      [denoteGraph pm initPM 3387, denoteGraph pm initPM 3390,
       denoteGraph pm initPM 3393, denoteGraph pm initPM 3396] := by
    rw [h256_REC]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hgr0_sh]; intro hc; cases hc
  have h105 := prove_pattern_21 (target := goal_105_stmt) pattern_21_target.goal_105
    initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h105_SH, _, h105_REC⟩ := h105
  simp only [goal_105, List.map_cons, List.map_nil, reconstructWithDim_singleton] at h105_REC
  have h105_SH' : (denoteGraph sm initSM 710).shape = [1, 8, 32] := by
    have := h105_SH; simp only [goal_105] at this; exact this
  have h711_init := hInitGoals initGoal_711 (by simp [initGoals])
  obtain ⟨h711_sh, hw_sh, h711_rec⟩ := h711_init
  simp only [initGoal_711, List.map_cons, List.map_nil] at h711_rec hw_sh
  have hwr0_sh : (initPM 3369).shape = [32, 32] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.1
  have h711_dimN : initSM 711 = allGatherPrimDimN 0 pm.numRanks 0
      [initPM 3369, initPM 3370, initPM 3371, initPM 3372] := by
    rw [h711_rec]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hwr0_sh]; intro hc; cases hc
  have H711 := sm254_init_711 initSM
  have H3369 := pm254_init_3369 initPM
  have H3370 := pm254_init_3370 initPM
  have H3371 := pm254_init_3371 initPM
  have H3372 := pm254_init_3372 initPM
  have hS := sm254_eval_893 initSM
  have hP0 := pm254_eval_3394 initPM
  have hP1 := pm254_eval_3391 initPM
  have hP2 := pm254_eval_3388 initPM
  have hP3 := pm254_eval_3385 initPM
  have hPar := pm254_eval_893 initPM
  have h711_sh' : (denoteGraph sm initSM 711).shape = [128, 32] := by
    rw [H711]; have := h711_sh; simp only [initGoal_711] at this; exact this
  have hwr0_pm_sh : (denoteGraph pm initPM 3369).shape = [32, 32] := by
    rw [H3369]; exact hwr0_sh
  have hwr1_pm_sh : (denoteGraph pm initPM 3370).shape = [32, 32] := by
    rw [H3370]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.1
  have hwr2_pm_sh : (denoteGraph pm initPM 3371).shape = [32, 32] := by
    rw [H3371]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.1
  have hwr3_pm_sh : (denoteGraph pm initPM 3372).shape = [32, 32] := by
    rw [H3372]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  have h105_PM_SH : (denoteGraph pm initPM 710).shape = [1, 8, 32] := by
    rw [← h105_REC]; exact h105_SH'
  have h256_SH' : (denoteGraph sm initSM 895).shape = [1, 8, 128] := by
    have := h256_SH; simp only [goal_256] at this; exact this
  have hLHS_sh : (denoteGraph sm initSM 893).shape = [1, 8, 32] := by
    rw [hS]
    exact bw_linear_3d_fst_shape 1 8 128 32 _ _ _ h256_SH' h105_SH' h711_sh'
  have hbridge := bridge_dX_4 1 8 32 32
      (denoteGraph pm initPM 3387) (denoteGraph pm initPM 3390)
      (denoteGraph pm initPM 3393) (denoteGraph pm initPM 3396)
      (denoteGraph pm initPM 710)
      (denoteGraph pm initPM 3369) (denoteGraph pm initPM 3370)
      (denoteGraph pm initPM 3371) (denoteGraph pm initPM 3372)
      hgr0_sh hgr1_sh hgr2_sh hgr3_sh
      hwr0_pm_sh hwr1_pm_sh hwr2_pm_sh hwr3_pm_sh
      h105_PM_SH (by decide) (by decide)
  have hP0_sh : (denoteGraph pm initPM 3394).shape = [1, 8, 32] := by
    rw [hP0]
    exact bw_linear_3d_fst_shape 1 8 32 32 _ _ _ hgr0_sh h105_PM_SH hwr0_pm_sh
  have hP1_sh : (denoteGraph pm initPM 3391).shape = [1, 8, 32] := by
    rw [hP1]
    exact bw_linear_3d_fst_shape 1 8 32 32 _ _ _ hgr1_sh h105_PM_SH hwr1_pm_sh
  have hP2_sh : (denoteGraph pm initPM 3388).shape = [1, 8, 32] := by
    rw [hP2]
    exact bw_linear_3d_fst_shape 1 8 32 32 _ _ _ hgr2_sh h105_PM_SH hwr2_pm_sh
  have hP3_sh : (denoteGraph pm initPM 3385).shape = [1, 8, 32] := by
    rw [hP3]
    exact bw_linear_3d_fst_shape 1 8 32 32 _ _ _ hgr3_sh h105_PM_SH hwr3_pm_sh
  have hnr : pm.numRanks = 4 := rfl
  have h256_DIMN4 : denoteGraph sm initSM 895 = allGatherPrimDimN 2 4 0
      [denoteGraph pm initPM 3387, denoteGraph pm initPM 3390,
       denoteGraph pm initPM 3393, denoteGraph pm initPM 3396] := by
    rw [h256_DIMN, hnr]
  have h711_dimN4 : denoteGraph sm initSM 711 = allGatherPrimDimN 0 4 0
      [denoteGraph pm initPM 3369, denoteGraph pm initPM 3370,
       denoteGraph pm initPM 3371, denoteGraph pm initPM 3372] := by
    rw [H711, h711_dimN, hnr, H3369, H3370, H3371, H3372]
  have h893_eq : denoteGraph sm initSM 893 = denoteGraph pm initPM 893 := by
    rw [hS, h256_DIMN4, h105_REC, h711_dimN4, hbridge, hPar, hnr]
    simp only [List.map_cons, List.map_nil]
    rw [← hP0, ← hP1, ← hP2, ← hP3]
  have h893_pm_sh : (denoteGraph pm initPM 893).shape = [1, 8, 32] := by
    rw [← h893_eq]; exact hLHS_sh
  have hC0 := pm254_eval_3359 initPM
  have hC1 := pm254_eval_3362 initPM
  have hC2 := pm254_eval_3365 initPM
  have hC3 := pm254_eval_3368 initPM
  have hC0_sh : (denoteGraph pm initPM 3359).shape = [1, 2, 32] := by
    rw [hC0, hnr]; exact chunkPrimDimN_1_4_shape _ 32 0 h893_pm_sh
  have hC1_sh : (denoteGraph pm initPM 3362).shape = [1, 2, 32] := by
    rw [hC1, hnr]; exact chunkPrimDimN_1_4_shape _ 32 1 h893_pm_sh
  have hC2_sh : (denoteGraph pm initPM 3365).shape = [1, 2, 32] := by
    rw [hC2, hnr]; exact chunkPrimDimN_1_4_shape _ 32 2 h893_pm_sh
  have hC3_sh : (denoteGraph pm initPM 3368).shape = [1, 2, 32] := by
    rw [hC3, hnr]; exact chunkPrimDimN_1_4_shape _ 32 3 h893_pm_sh
  refine ⟨?_, ?_, ?_⟩
  · show (denoteGraph sm initSM 893).shape = [1, 8, 32]; exact hLHS_sh
  · show List.map (fun t => Tensor.shape t)
        ([({ rank := 0, tid := 3359 } : Piece),
          ({ rank := 1, tid := 3362 } : Piece),
          ({ rank := 2, tid := 3365 } : Piece),
          ({ rank := 3, tid := 3368 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]]
    simp only [List.map_cons, List.map_nil]
    rw [hC0_sh, hC1_sh, hC2_sh, hC3_sh]
  · show denoteGraph sm initSM 893 =
        reconstructWithDim 1 pm.numRanks 0
          ([({ rank := 0, tid := 3359 } : Piece),
            ({ rank := 1, tid := 3362 } : Piece),
            ({ rank := 2, tid := 3365 } : Piece),
            ({ rank := 3, tid := 3368 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
    simp only [List.map_cons, List.map_nil]
    rw [hnr]
    rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _
      (by rw [hC0_sh]; intro hc; cases hc)]
    rw [hC0, hC1, hC2, hC3, hnr]
    rw [h893_eq]
    exact (gather_chunk_dim1_1_8_32 _ h893_pm_sh).symm

theorem prove_pattern_78 : pattern_78_stmt := by
  intro target h
  cases h with
  | goal_140 => exact prove_goal_140
  | goal_175 => exact prove_goal_175
  | goal_178 => exact prove_goal_178
  | goal_254 => exact prove_goal_254

end TrainVerify.Denote.GeneratedPatterns

