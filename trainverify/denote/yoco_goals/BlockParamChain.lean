/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L12FaithfulLinearChain

/-!
# Parameterised block main-chain reduction (6 nodes)

Extends `denote/yoco_goals/BlockParamSpike.lean` from a 3-node window to the
front segment of a cross-decoder block's main chain:

  `FW_reshape → FW_reshape → FW_mix_precision_linear → FW_view → FW_float → FW_add`

Design notes (carried over from the spike):
* node-literal facts are stated in `getElem?` form so `native_decide` applies;
  `getElem_of_getElem?'` converts back;
* the three op-name side conditions of
  `applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective`
  are given as explicit `show ("OpName.XXX" : String) ≠ _ by decide`;
* the `not-written` side conditions are split into FOUR small per-op-kind
  structures (`ChainNWReshape`, `ChainNWLinear`, `ChainNWViewFloat`,
  `ChainNWAdd`) which are then combined in `ChainNotWritten`, so no single
  `where` block gets large;
* node indices are *not* assumed contiguous (the PM graph interleaves the two
  ranks, so per-rank indices have stride 2): every node carries its own index
  field.

Instantiations (6 total, all from the real generated graphs):
* block 0 / SM      : nodes 506–511
* block 1 / SM      : nodes 541–546
* block 0 / PM rank0: nodes 1074,1076,1078,1080,1082,1084
* block 0 / PM rank1: nodes 1075,1077,1079,1081,1083,1085
* block 1 / PM rank0: nodes 1144,1146,1148,1150,1152,1154
* block 1 / PM rank1: nodes 1145,1147,1149,1151,1153,1155
-/

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false

namespace TrainVerify.Denote.BlockParamChain

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.GeneratedPatterns

noncomputable section

/-! ### 1. Coordinate bundle -/

/-- Per-block coordinates of the 6-node main-chain front segment
`reshape ; reshape ; linear ; view ; float ; add`.

Tensor ids: `t0 --reshape--> t1 --reshape--> t2 --linear(tW)--> t3 --view--> t4
--float--> t5 --add(tRes)--> t6`. -/
structure ChainTids where
  /-- index of the first `FW_reshape` -/
  kR1 : Nat
  /-- index of the second `FW_reshape` -/
  kR2 : Nat
  /-- index of the `FW_mix_precision_linear` -/
  kL : Nat
  /-- index of the `FW_view` -/
  kV : Nat
  /-- index of the `FW_float` -/
  kF : Nat
  /-- index of the `FW_add` -/
  kA : Nat
  /-- rank the six nodes live on -/
  rank : Nat
  /-- attention output, input of the first reshape -/
  t0 : Tid
  /-- output of the first reshape -/
  t1 : Tid
  /-- output of the second reshape -/
  t2 : Tid
  /-- replicated projection weight -/
  tW : Tid
  /-- output of the linear -/
  t3 : Tid
  /-- output of the view -/
  t4 : Tid
  /-- output of the float -/
  t5 : Tid
  /-- residual stream, first input of the add -/
  tRes : Tid
  /-- output of the add -/
  t6 : Tid
  /-- head of the (non-empty) shape parameter list -/
  vhd : Nat
  /-- tail of the shape parameter list -/
  vtl : List Nat

namespace ChainTids

variable (T : ChainTids)

/-- shape parameter list, non-empty by construction -/
def vsh : List Nat := T.vhd :: T.vtl

def nR1 : NodeDecl :=
  { rank := T.rank, op := "OpName.FW_reshape", ins := [T.t0], outs := [T.t1],
    params := T.vhd :: T.vtl }

def nR2 : NodeDecl :=
  { rank := T.rank, op := "OpName.FW_reshape", ins := [T.t1], outs := [T.t2],
    params := T.vhd :: T.vtl }

def nL : NodeDecl :=
  { rank := T.rank, op := "OpName.FW_mix_precision_linear", ins := [T.t2, T.tW],
    outs := [T.t3] }

def nV : NodeDecl :=
  { rank := T.rank, op := "OpName.FW_view", ins := [T.t3], outs := [T.t4],
    params := T.vhd :: T.vtl }

def nF : NodeDecl :=
  { rank := T.rank, op := "OpName.FW_float", ins := [T.t4], outs := [T.t5] }

def nA : NodeDecl :=
  { rank := T.rank, op := "OpName.FW_add", ins := [T.tRes, T.t5], outs := [T.t6] }

end ChainTids

/-! ### 2. Side conditions, split per op kind -/

/-- Side conditions for the two `FW_reshape` nodes. -/
structure ChainNWReshape (g : GraphDecl) (T : ChainTids) : Prop where
  hkR1 : T.kR1 < g.nodes.length
  hkR2 : T.kR2 < g.nodes.length
  /-- attention output is stable from the first reshape onwards -/
  w0 : ∀ n ∈ g.nodes.drop T.kR1, T.t0 ∉ n.outs
  /-- first reshape output is not rewritten later -/
  w1a : ∀ n ∈ g.nodes.drop (T.kR1 + 1), T.t1 ∉ n.outs
  /-- ... and in particular stable from the second reshape onwards -/
  w1b : ∀ n ∈ g.nodes.drop T.kR2, T.t1 ∉ n.outs
  /-- second reshape output is not rewritten later -/
  w2a : ∀ n ∈ g.nodes.drop (T.kR2 + 1), T.t2 ∉ n.outs

/-- Side conditions for the `FW_mix_precision_linear` node. -/
structure ChainNWLinear (g : GraphDecl) (T : ChainTids) : Prop where
  hkL : T.kL < g.nodes.length
  /-- linear's data input is stable from the linear onwards -/
  w2b : ∀ n ∈ g.nodes.drop T.kL, T.t2 ∉ n.outs
  /-- weight is stable from the linear onwards -/
  wW : ∀ n ∈ g.nodes.drop T.kL, T.tW ∉ n.outs
  /-- linear output is not rewritten later -/
  w3a : ∀ n ∈ g.nodes.drop (T.kL + 1), T.t3 ∉ n.outs

/-- Side conditions for the `FW_view` and `FW_float` nodes. -/
structure ChainNWViewFloat (g : GraphDecl) (T : ChainTids) : Prop where
  hkV : T.kV < g.nodes.length
  hkF : T.kF < g.nodes.length
  w3b : ∀ n ∈ g.nodes.drop T.kV, T.t3 ∉ n.outs
  w4a : ∀ n ∈ g.nodes.drop (T.kV + 1), T.t4 ∉ n.outs
  w4b : ∀ n ∈ g.nodes.drop T.kF, T.t4 ∉ n.outs
  w5a : ∀ n ∈ g.nodes.drop (T.kF + 1), T.t5 ∉ n.outs

/-- Side conditions for the residual `FW_add` node. -/
structure ChainNWAdd (g : GraphDecl) (T : ChainTids) : Prop where
  hkA : T.kA < g.nodes.length
  w5b : ∀ n ∈ g.nodes.drop T.kA, T.t5 ∉ n.outs
  wRes : ∀ n ∈ g.nodes.drop T.kA, T.tRes ∉ n.outs
  w6 : ∀ n ∈ g.nodes.drop (T.kA + 1), T.t6 ∉ n.outs

/-- All side conditions, combined.  `nilAll` is a graph-wide fact, so it is
supplied once instead of per node. -/
structure ChainNotWritten (g : GraphDecl) (T : ChainTids) : Prop where
  nilAll : ∀ n ∈ g.nodes, n.outs ≠ []
  res : ChainNWReshape g T
  lin : ChainNWLinear g T
  vf : ChainNWViewFloat g T
  add : ChainNWAdd g T

/-- The six node-literal facts, in `getElem?` form (so `native_decide` works). -/
structure ChainNodes (g : GraphDecl) (T : ChainTids) : Prop where
  hR1 : g.nodes[T.kR1]? = some T.nR1
  hR2 : g.nodes[T.kR2]? = some T.nR2
  hL : g.nodes[T.kL]? = some T.nL
  hV : g.nodes[T.kV]? = some T.nV
  hF : g.nodes[T.kF]? = some T.nF
  hA : g.nodes[T.kA]? = some T.nA

/-- Turn a `getElem?` fact into the `getElem` fact the `reduceN` lemmas expect. -/
theorem getElem_of_getElem?' {α : Type _} (l : List α) (i : Nat) (a : α)
    (h : l[i]? = some a) (hi : i < l.length) : l[i]'hi = a :=
  Option.some.inj (by rw [← List.getElem?_eq_getElem hi, h])

/-- Derive the `drop`-restricted nonempty condition from the graph-wide one. -/
theorem nil_drop {g : GraphDecl} (h : ∀ n ∈ g.nodes, n.outs ≠ []) (k : Nat) :
    ∀ n ∈ g.nodes.drop k, n.outs ≠ [] :=
  fun n hn => h n (List.mem_of_mem_drop hn)

/-! ### 3. Parameterised reductions, one per op kind -/

/-- Reduction of a chain `FW_reshape` node (params non-empty ⇒ acts as `fw_view`). -/
theorem chain_reduce_reshape (g : GraphDecl) (init : Store) (T : ChainTids)
    (nilAll : ∀ n ∈ g.nodes, n.outs ≠ [])
    (k : Nat) (hk : k < g.nodes.length) (tIn tOut : Tid)
    (hnode : g.nodes[k]? = some
      { rank := T.rank, op := "OpName.FW_reshape", ins := [tIn], outs := [tOut],
        params := T.vhd :: T.vtl })
    (hafter : ∀ n ∈ g.nodes.drop (k + 1), tOut ∉ n.outs)
    (hpre : ∀ n ∈ g.nodes.drop k, tIn ∉ n.outs) :
    denoteGraphDistributedFaithful g init tOut =
      fw_view (T.vhd :: T.vtl) (denoteGraphDistributedFaithful g init tIn) := by
  refine denoteGraphDistributedFaithful_reduce1 g init k _ tIn tOut
    (fun x => fw_view (T.vhd :: T.vtl) x) hk
    (getElem_of_getElem?' _ _ _ hnode hk) ?_ (nil_drop nilAll (k + 1)) hafter
    (nil_drop nilAll k) hpre
  intro s
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (show ("OpName.FW_reshape" : String) ≠ _ by decide)
    (show ("OpName.FW_reshape" : String) ≠ _ by decide)
    (show ("OpName.FW_reshape" : String) ≠ _ by decide)]
  exact applyNode_fw_reshape_out g s T.rank tIn tOut (T.vhd :: T.vtl)

/-- Reduction of the chain `FW_view` node. -/
theorem chain_reduce_view (g : GraphDecl) (init : Store) (T : ChainTids)
    (nilAll : ∀ n ∈ g.nodes, n.outs ≠ [])
    (k : Nat) (hk : k < g.nodes.length) (tIn tOut : Tid)
    (hnode : g.nodes[k]? = some
      { rank := T.rank, op := "OpName.FW_view", ins := [tIn], outs := [tOut],
        params := T.vhd :: T.vtl })
    (hafter : ∀ n ∈ g.nodes.drop (k + 1), tOut ∉ n.outs)
    (hpre : ∀ n ∈ g.nodes.drop k, tIn ∉ n.outs) :
    denoteGraphDistributedFaithful g init tOut =
      fw_view (T.vhd :: T.vtl) (denoteGraphDistributedFaithful g init tIn) := by
  refine denoteGraphDistributedFaithful_reduce1 g init k _ tIn tOut
    (fun x => fw_view (T.vhd :: T.vtl) x) hk
    (getElem_of_getElem?' _ _ _ hnode hk) ?_ (nil_drop nilAll (k + 1)) hafter
    (nil_drop nilAll k) hpre
  intro s
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (show ("OpName.FW_view" : String) ≠ _ by decide)
    (show ("OpName.FW_view" : String) ≠ _ by decide)
    (show ("OpName.FW_view" : String) ≠ _ by decide)]
  exact applyNode_fw_view_out g s T.rank T.vhd T.vtl tIn tOut

/-- Reduction of the chain `FW_float` node (identity on `Scalar = ℝ`). -/
theorem chain_reduce_float (g : GraphDecl) (init : Store) (T : ChainTids)
    (nilAll : ∀ n ∈ g.nodes, n.outs ≠ [])
    (k : Nat) (hk : k < g.nodes.length) (tIn tOut : Tid)
    (hnode : g.nodes[k]? = some
      { rank := T.rank, op := "OpName.FW_float", ins := [tIn], outs := [tOut] })
    (hafter : ∀ n ∈ g.nodes.drop (k + 1), tOut ∉ n.outs)
    (hpre : ∀ n ∈ g.nodes.drop k, tIn ∉ n.outs) :
    denoteGraphDistributedFaithful g init tOut =
      denoteGraphDistributedFaithful g init tIn := by
  refine denoteGraphDistributedFaithful_reduce1 g init k _ tIn tOut
    (fun x => x) hk
    (getElem_of_getElem?' _ _ _ hnode hk) ?_ (nil_drop nilAll (k + 1)) hafter
    (nil_drop nilAll k) hpre
  intro s
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (show ("OpName.FW_float" : String) ≠ _ by decide)
    (show ("OpName.FW_float" : String) ≠ _ by decide)
    (show ("OpName.FW_float" : String) ≠ _ by decide)]
  exact applyNode_fw_float_out g s T.rank tIn tOut []

/-- Reduction of the chain `FW_mix_precision_linear` node. -/
theorem chain_reduce_linear (g : GraphDecl) (init : Store) (T : ChainTids)
    (nilAll : ∀ n ∈ g.nodes, n.outs ≠ [])
    (k : Nat) (hk : k < g.nodes.length) (tIn tWt tOut : Tid)
    (hnode : g.nodes[k]? = some
      { rank := T.rank, op := "OpName.FW_mix_precision_linear", ins := [tIn, tWt],
        outs := [tOut] })
    (hafter : ∀ n ∈ g.nodes.drop (k + 1), tOut ∉ n.outs)
    (hpre : ∀ n ∈ g.nodes.drop k, tIn ∉ n.outs)
    (hpreW : ∀ n ∈ g.nodes.drop k, tWt ∉ n.outs) :
    denoteGraphDistributedFaithful g init tOut =
      fw_linear (denoteGraphDistributedFaithful g init tIn)
        (denoteGraphDistributedFaithful g init tWt) := by
  refine denoteGraphDistributedFaithful_reduce2 g init k _ tIn tWt tOut fw_linear hk
    (getElem_of_getElem?' _ _ _ hnode hk) ?_ (nil_drop nilAll (k + 1)) hafter
    (nil_drop nilAll k) hpre hpreW
  intro s
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (show ("OpName.FW_mix_precision_linear" : String) ≠ _ by decide)
    (show ("OpName.FW_mix_precision_linear" : String) ≠ _ by decide)
    (show ("OpName.FW_mix_precision_linear" : String) ≠ _ by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p g s T.rank tIn tWt tOut

/-- Reduction of the chain residual `FW_add` node. -/
theorem chain_reduce_add (g : GraphDecl) (init : Store) (T : ChainTids)
    (nilAll : ∀ n ∈ g.nodes, n.outs ≠ [])
    (k : Nat) (hk : k < g.nodes.length) (tX tY tOut : Tid)
    (hnode : g.nodes[k]? = some
      { rank := T.rank, op := "OpName.FW_add", ins := [tX, tY], outs := [tOut] })
    (hafter : ∀ n ∈ g.nodes.drop (k + 1), tOut ∉ n.outs)
    (hpreX : ∀ n ∈ g.nodes.drop k, tX ∉ n.outs)
    (hpreY : ∀ n ∈ g.nodes.drop k, tY ∉ n.outs) :
    denoteGraphDistributedFaithful g init tOut =
      elemwiseAdd (denoteGraphDistributedFaithful g init tX)
        (denoteGraphDistributedFaithful g init tY) := by
  refine denoteGraphDistributedFaithful_reduce2 g init k _ tX tY tOut elemwiseAdd hk
    (getElem_of_getElem?' _ _ _ hnode hk) ?_ (nil_drop nilAll (k + 1)) hafter
    (nil_drop nilAll k) hpreX hpreY
  intro s
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (show ("OpName.FW_add" : String) ≠ _ by decide)
    (show ("OpName.FW_add" : String) ≠ _ by decide)
    (show ("OpName.FW_add" : String) ≠ _ by decide)]
  exact applyNode_fw_add2_out g s T.rank tX tY tOut

/-! ### 4. The parameterised 6-node chain theorem -/

/-- CORE: the full 6-equation reduction of the block main-chain front segment,
for an arbitrary graph, arbitrary rank and arbitrary block coordinates. -/
theorem chain_reduce6 (g : GraphDecl) (init : Store) (T : ChainTids)
    (NW : ChainNotWritten g T) (HN : ChainNodes g T) :
    denoteGraphDistributedFaithful g init T.t1 =
        fw_view (T.vhd :: T.vtl) (denoteGraphDistributedFaithful g init T.t0) ∧
      denoteGraphDistributedFaithful g init T.t2 =
        fw_view (T.vhd :: T.vtl) (denoteGraphDistributedFaithful g init T.t1) ∧
      denoteGraphDistributedFaithful g init T.t3 =
        fw_linear (denoteGraphDistributedFaithful g init T.t2)
          (denoteGraphDistributedFaithful g init T.tW) ∧
      denoteGraphDistributedFaithful g init T.t4 =
        fw_view (T.vhd :: T.vtl) (denoteGraphDistributedFaithful g init T.t3) ∧
      denoteGraphDistributedFaithful g init T.t5 =
        denoteGraphDistributedFaithful g init T.t4 ∧
      denoteGraphDistributedFaithful g init T.t6 =
        elemwiseAdd (denoteGraphDistributedFaithful g init T.tRes)
          (denoteGraphDistributedFaithful g init T.t5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact chain_reduce_reshape g init T NW.nilAll T.kR1 NW.res.hkR1 T.t0 T.t1
      HN.hR1 NW.res.w1a NW.res.w0
  · exact chain_reduce_reshape g init T NW.nilAll T.kR2 NW.res.hkR2 T.t1 T.t2
      HN.hR2 NW.res.w2a NW.res.w1b
  · exact chain_reduce_linear g init T NW.nilAll T.kL NW.lin.hkL T.t2 T.tW T.t3
      HN.hL NW.lin.w3a NW.lin.w2b NW.lin.wW
  · exact chain_reduce_view g init T NW.nilAll T.kV NW.vf.hkV T.t3 T.t4
      HN.hV NW.vf.w4a NW.vf.w3b
  · exact chain_reduce_float g init T NW.nilAll T.kF NW.vf.hkF T.t4 T.t5
      HN.hF NW.vf.w5a NW.vf.w4b
  · exact chain_reduce_add g init T NW.nilAll T.kA NW.add.hkA T.tRes T.t5 T.t6
      HN.hA NW.add.w6 NW.add.wRes NW.add.w5b

/-! ### 5. Instantiation: block 0 on the single-machine graph (nodes 506–511) -/

def sm_blk0 : ChainTids :=
  { kR1 := 506, kR2 := 507, kL := 508, kV := 509, kF := 510, kA := 511, rank := 0,
    t0 := 5347, t1 := 5348, t2 := 5349, tW := 5350, t3 := 5351, t4 := 5352,
    t5 := 5353, tRes := 8143, t6 := 5354, vhd := 4096, vtl := [1024] }

theorem sm_blk0_nodes : ChainNodes sm sm_blk0 := by
  constructor <;> native_decide

theorem sm_blk0_nw : ChainNotWritten sm sm_blk0 where
  nilAll := layer1_sm_nodes_nonempty
  res :=
    { hkR1 := by native_decide, hkR2 := by native_decide
      w0 := by native_decide +revert
      w1a := by native_decide +revert
      w1b := by native_decide +revert
      w2a := by native_decide +revert }
  lin :=
    { hkL := by native_decide
      w2b := by native_decide +revert
      wW := by native_decide +revert
      w3a := by native_decide +revert }
  vf :=
    { hkV := by native_decide, hkF := by native_decide
      w3b := by native_decide +revert
      w4a := by native_decide +revert
      w4b := by native_decide +revert
      w5a := by native_decide +revert }
  add :=
    { hkA := by native_decide
      w5b := by native_decide +revert
      wRes := by native_decide +revert
      w6 := by native_decide +revert }

theorem sm_blk0_chain (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5348 =
        fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5347) ∧
      denoteGraphDistributedFaithful sm initSM 5349 =
        fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5348) ∧
      denoteGraphDistributedFaithful sm initSM 5351 =
        fw_linear (denoteGraphDistributedFaithful sm initSM 5349)
          (denoteGraphDistributedFaithful sm initSM 5350) ∧
      denoteGraphDistributedFaithful sm initSM 5352 =
        fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5351) ∧
      denoteGraphDistributedFaithful sm initSM 5353 =
        denoteGraphDistributedFaithful sm initSM 5352 ∧
      denoteGraphDistributedFaithful sm initSM 5354 =
        elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8143)
          (denoteGraphDistributedFaithful sm initSM 5353) :=
  chain_reduce6 sm initSM sm_blk0 sm_blk0_nw sm_blk0_nodes

/-! ### 6. Instantiation: block 1 on the single-machine graph (nodes 541–546) -/

def sm_blk1 : ChainTids :=
  { kR1 := 541, kR2 := 542, kL := 543, kV := 544, kF := 545, kA := 546, rank := 0,
    t0 := 5396, t1 := 5397, t2 := 5398, tW := 5399, t3 := 5400, t4 := 5401,
    t5 := 5402, tRes := 8182, t6 := 5403, vhd := 4096, vtl := [1024] }

theorem sm_blk1_nodes : ChainNodes sm sm_blk1 := by
  constructor <;> native_decide

theorem sm_blk1_nw : ChainNotWritten sm sm_blk1 where
  nilAll := layer1_sm_nodes_nonempty
  res :=
    { hkR1 := by native_decide, hkR2 := by native_decide
      w0 := by native_decide +revert
      w1a := by native_decide +revert
      w1b := by native_decide +revert
      w2a := by native_decide +revert }
  lin :=
    { hkL := by native_decide
      w2b := by native_decide +revert
      wW := by native_decide +revert
      w3a := by native_decide +revert }
  vf :=
    { hkV := by native_decide, hkF := by native_decide
      w3b := by native_decide +revert
      w4a := by native_decide +revert
      w4b := by native_decide +revert
      w5a := by native_decide +revert }
  add :=
    { hkA := by native_decide
      w5b := by native_decide +revert
      wRes := by native_decide +revert
      w6 := by native_decide +revert }

theorem sm_blk1_chain (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5397 =
        fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5396) ∧
      denoteGraphDistributedFaithful sm initSM 5398 =
        fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5397) ∧
      denoteGraphDistributedFaithful sm initSM 5400 =
        fw_linear (denoteGraphDistributedFaithful sm initSM 5398)
          (denoteGraphDistributedFaithful sm initSM 5399) ∧
      denoteGraphDistributedFaithful sm initSM 5401 =
        fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5400) ∧
      denoteGraphDistributedFaithful sm initSM 5402 =
        denoteGraphDistributedFaithful sm initSM 5401 ∧
      denoteGraphDistributedFaithful sm initSM 5403 =
        elemwiseAdd (denoteGraphDistributedFaithful sm initSM 8182)
          (denoteGraphDistributedFaithful sm initSM 5402) :=
  chain_reduce6 sm initSM sm_blk1 sm_blk1_nw sm_blk1_nodes

/-! ### 7. Instantiation: block 0 on the parallel-machine graph, both ranks -/

def pm_blk0_r0 : ChainTids :=
  { kR1 := 1074, kR2 := 1076, kL := 1078, kV := 1080, kF := 1082, kA := 1084, rank := 0,
    t0 := 9687, t1 := 9689, t2 := 9695, tW := 5350, t3 := 9699, t4 := 9709,
    t5 := 9713, tRes := 15973, t6 := 9717, vhd := 2048, vtl := [1024] }

def pm_blk0_r1 : ChainTids :=
  { kR1 := 1075, kR2 := 1077, kL := 1079, kV := 1081, kF := 1083, kA := 1085, rank := 1,
    t0 := 9688, t1 := 9690, t2 := 9696, tW := 5350, t3 := 9700, t4 := 9710,
    t5 := 9714, tRes := 15981, t6 := 9718, vhd := 2048, vtl := [1024] }

theorem pm_blk0_r0_nodes : ChainNodes pm pm_blk0_r0 := by
  constructor <;> native_decide

theorem pm_blk0_r1_nodes : ChainNodes pm pm_blk0_r1 := by
  constructor <;> native_decide

theorem pm_blk0_r0_nw : ChainNotWritten pm pm_blk0_r0 where
  nilAll := layer1_pm_nodes_nonempty
  res :=
    { hkR1 := by native_decide, hkR2 := by native_decide
      w0 := by native_decide +revert
      w1a := by native_decide +revert
      w1b := by native_decide +revert
      w2a := by native_decide +revert }
  lin :=
    { hkL := by native_decide
      w2b := by native_decide +revert
      wW := by native_decide +revert
      w3a := by native_decide +revert }
  vf :=
    { hkV := by native_decide, hkF := by native_decide
      w3b := by native_decide +revert
      w4a := by native_decide +revert
      w4b := by native_decide +revert
      w5a := by native_decide +revert }
  add :=
    { hkA := by native_decide
      w5b := by native_decide +revert
      wRes := by native_decide +revert
      w6 := by native_decide +revert }

theorem pm_blk0_r1_nw : ChainNotWritten pm pm_blk0_r1 where
  nilAll := layer1_pm_nodes_nonempty
  res :=
    { hkR1 := by native_decide, hkR2 := by native_decide
      w0 := by native_decide +revert
      w1a := by native_decide +revert
      w1b := by native_decide +revert
      w2a := by native_decide +revert }
  lin :=
    { hkL := by native_decide
      w2b := by native_decide +revert
      wW := by native_decide +revert
      w3a := by native_decide +revert }
  vf :=
    { hkV := by native_decide, hkF := by native_decide
      w3b := by native_decide +revert
      w4a := by native_decide +revert
      w4b := by native_decide +revert
      w5a := by native_decide +revert }
  add :=
    { hkA := by native_decide
      w5b := by native_decide +revert
      wRes := by native_decide +revert
      w6 := by native_decide +revert }

theorem pm_blk0_r0_chain (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9689 =
        fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9687) ∧
      denoteGraphDistributedFaithful pm initPM 9695 =
        fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9689) ∧
      denoteGraphDistributedFaithful pm initPM 9699 =
        fw_linear (denoteGraphDistributedFaithful pm initPM 9695)
          (denoteGraphDistributedFaithful pm initPM 5350) ∧
      denoteGraphDistributedFaithful pm initPM 9709 =
        fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9699) ∧
      denoteGraphDistributedFaithful pm initPM 9713 =
        denoteGraphDistributedFaithful pm initPM 9709 ∧
      denoteGraphDistributedFaithful pm initPM 9717 =
        elemwiseAdd (denoteGraphDistributedFaithful pm initPM 15973)
          (denoteGraphDistributedFaithful pm initPM 9713) :=
  chain_reduce6 pm initPM pm_blk0_r0 pm_blk0_r0_nw pm_blk0_r0_nodes

theorem pm_blk0_r1_chain (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9690 =
        fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9688) ∧
      denoteGraphDistributedFaithful pm initPM 9696 =
        fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9690) ∧
      denoteGraphDistributedFaithful pm initPM 9700 =
        fw_linear (denoteGraphDistributedFaithful pm initPM 9696)
          (denoteGraphDistributedFaithful pm initPM 5350) ∧
      denoteGraphDistributedFaithful pm initPM 9710 =
        fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9700) ∧
      denoteGraphDistributedFaithful pm initPM 9714 =
        denoteGraphDistributedFaithful pm initPM 9710 ∧
      denoteGraphDistributedFaithful pm initPM 9718 =
        elemwiseAdd (denoteGraphDistributedFaithful pm initPM 15981)
          (denoteGraphDistributedFaithful pm initPM 9714) :=
  chain_reduce6 pm initPM pm_blk0_r1 pm_blk0_r1_nw pm_blk0_r1_nodes

/-! ### 8. Instantiation: block 1 on the parallel-machine graph, both ranks -/

def pm_blk1_r0 : ChainTids :=
  { kR1 := 1144, kR2 := 1146, kL := 1148, kV := 1150, kF := 1152, kA := 1154, rank := 0,
    t0 := 9859, t1 := 9861, t2 := 9867, tW := 5399, t3 := 9871, t4 := 9881,
    t5 := 9885, tRes := 16051, t6 := 9889, vhd := 2048, vtl := [1024] }

def pm_blk1_r1 : ChainTids :=
  { kR1 := 1145, kR2 := 1147, kL := 1149, kV := 1151, kF := 1153, kA := 1155, rank := 1,
    t0 := 9860, t1 := 9862, t2 := 9868, tW := 5399, t3 := 9872, t4 := 9882,
    t5 := 9886, tRes := 16059, t6 := 9890, vhd := 2048, vtl := [1024] }

theorem pm_blk1_r0_nodes : ChainNodes pm pm_blk1_r0 := by
  constructor <;> native_decide

theorem pm_blk1_r1_nodes : ChainNodes pm pm_blk1_r1 := by
  constructor <;> native_decide

theorem pm_blk1_r0_nw : ChainNotWritten pm pm_blk1_r0 where
  nilAll := layer1_pm_nodes_nonempty
  res :=
    { hkR1 := by native_decide, hkR2 := by native_decide
      w0 := by native_decide +revert
      w1a := by native_decide +revert
      w1b := by native_decide +revert
      w2a := by native_decide +revert }
  lin :=
    { hkL := by native_decide
      w2b := by native_decide +revert
      wW := by native_decide +revert
      w3a := by native_decide +revert }
  vf :=
    { hkV := by native_decide, hkF := by native_decide
      w3b := by native_decide +revert
      w4a := by native_decide +revert
      w4b := by native_decide +revert
      w5a := by native_decide +revert }
  add :=
    { hkA := by native_decide
      w5b := by native_decide +revert
      wRes := by native_decide +revert
      w6 := by native_decide +revert }

theorem pm_blk1_r1_nw : ChainNotWritten pm pm_blk1_r1 where
  nilAll := layer1_pm_nodes_nonempty
  res :=
    { hkR1 := by native_decide, hkR2 := by native_decide
      w0 := by native_decide +revert
      w1a := by native_decide +revert
      w1b := by native_decide +revert
      w2a := by native_decide +revert }
  lin :=
    { hkL := by native_decide
      w2b := by native_decide +revert
      wW := by native_decide +revert
      w3a := by native_decide +revert }
  vf :=
    { hkV := by native_decide, hkF := by native_decide
      w3b := by native_decide +revert
      w4a := by native_decide +revert
      w4b := by native_decide +revert
      w5a := by native_decide +revert }
  add :=
    { hkA := by native_decide
      w5b := by native_decide +revert
      wRes := by native_decide +revert
      w6 := by native_decide +revert }

theorem pm_blk1_r0_chain (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9861 =
        fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9859) ∧
      denoteGraphDistributedFaithful pm initPM 9867 =
        fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9861) ∧
      denoteGraphDistributedFaithful pm initPM 9871 =
        fw_linear (denoteGraphDistributedFaithful pm initPM 9867)
          (denoteGraphDistributedFaithful pm initPM 5399) ∧
      denoteGraphDistributedFaithful pm initPM 9881 =
        fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9871) ∧
      denoteGraphDistributedFaithful pm initPM 9885 =
        denoteGraphDistributedFaithful pm initPM 9881 ∧
      denoteGraphDistributedFaithful pm initPM 9889 =
        elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16051)
          (denoteGraphDistributedFaithful pm initPM 9885) :=
  chain_reduce6 pm initPM pm_blk1_r0 pm_blk1_r0_nw pm_blk1_r0_nodes

theorem pm_blk1_r1_chain (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9862 =
        fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9860) ∧
      denoteGraphDistributedFaithful pm initPM 9868 =
        fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9862) ∧
      denoteGraphDistributedFaithful pm initPM 9872 =
        fw_linear (denoteGraphDistributedFaithful pm initPM 9868)
          (denoteGraphDistributedFaithful pm initPM 5399) ∧
      denoteGraphDistributedFaithful pm initPM 9882 =
        fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9872) ∧
      denoteGraphDistributedFaithful pm initPM 9886 =
        denoteGraphDistributedFaithful pm initPM 9882 ∧
      denoteGraphDistributedFaithful pm initPM 9890 =
        elemwiseAdd (denoteGraphDistributedFaithful pm initPM 16059)
          (denoteGraphDistributedFaithful pm initPM 9886) :=
  chain_reduce6 pm initPM pm_blk1_r1 pm_blk1_r1_nw pm_blk1_r1_nodes

end
end TrainVerify.Denote.BlockParamChain
