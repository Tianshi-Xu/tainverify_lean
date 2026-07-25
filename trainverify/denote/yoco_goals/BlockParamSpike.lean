/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L12FaithfulLinearChain

/-!
# SPIKE: parameterised block-level reduction lemma

Feasibility spike for the "12 isomorphic cross-decoder blocks" decision:
can we bundle the `not-written` / `nonempty` side conditions into a structure
and state ONE parameterised block-level chained reduction lemma, then
instantiate it per block?

The spike covers a 3-node window (reshape / mix_precision_linear / view),
which is exactly the window proved non-parametrically in
`denote/yoco_goals/L12FaithfulLinearChain.lean` for block 0
(SM nodes 507/508/509, tids 5348→5349→5351→5352).

We instantiate the parameterised lemma twice:
* block 0: SM nodes 507/508/509, tids 5348 / 5349 / 5350 / 5351 / 5352
* block 1: SM nodes 542/543/544, tids 5397 / 5398 / 5399 / 5400 / 5401

and derive statements definitionally identical to `l12lin_red_sm5349`,
`l12lin_red_sm5351`, `l12lin_red_sm5352`.
-/

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false

namespace TrainVerify.Denote.BlockParamSpike

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.GeneratedPatterns

noncomputable section

/-! ### 1. Tid / index bundle (mirrors a `BlockTids` record) -/

/-- Per-block coordinates of the 3-node `reshape ; linear ; view` window.
Node indices are contiguous: `k0`, `k0+1`, `k0+2`. -/
structure BlockTids where
  /-- index of the `FW_reshape` node -/
  k0 : Nat
  /-- rank of the three nodes (0 on the single-machine graph) -/
  rank : Nat
  /-- input of the reshape -/
  tIn : Tid
  /-- output of the reshape = first input of the linear -/
  tA : Tid
  /-- replicated weight, second input of the linear -/
  tW : Tid
  /-- output of the linear -/
  tB : Tid
  /-- output of the view -/
  tC : Tid
  /-- head of the shape parameter list (kept non-empty by construction) -/
  vhd : Nat
  /-- tail of the shape parameter list -/
  vtl : List Nat

/-- The three node literals determined by a `BlockTids`. -/
def BlockTids.nReshape (T : BlockTids) : NodeDecl :=
  { rank := T.rank, op := "OpName.FW_reshape", ins := [T.tIn], outs := [T.tA],
    params := T.vhd :: T.vtl }

def BlockTids.nLinear (T : BlockTids) : NodeDecl :=
  { rank := T.rank, op := "OpName.FW_mix_precision_linear", ins := [T.tA, T.tW],
    outs := [T.tB] }

def BlockTids.nView (T : BlockTids) : NodeDecl :=
  { rank := T.rank, op := "OpName.FW_view", ins := [T.tB], outs := [T.tC],
    params := T.vhd :: T.vtl }

/-! ### 2. The packed side-condition structure -/

/-- All `nonempty-outs` / `not-written` side conditions the three reductions need,
bundled into a single record so a block-level lemma can take them as ONE argument. -/
structure BlockNotWritten (g : GraphDecl) (T : BlockTids) : Prop where
  /-- the window fits inside the graph -/
  hlen : T.k0 + 2 < g.nodes.length
  nil0 : ∀ n ∈ g.nodes.drop T.k0, n.outs ≠ []
  nil1 : ∀ n ∈ g.nodes.drop (T.k0 + 1), n.outs ≠ []
  nil2 : ∀ n ∈ g.nodes.drop (T.k0 + 2), n.outs ≠ []
  nil3 : ∀ n ∈ g.nodes.drop (T.k0 + 3), n.outs ≠ []
  /-- reshape output is not rewritten later -/
  wA : ∀ n ∈ g.nodes.drop (T.k0 + 1), T.tA ∉ n.outs
  /-- reshape input is stable from the reshape onwards -/
  wIn : ∀ n ∈ g.nodes.drop T.k0, T.tIn ∉ n.outs
  /-- weight is stable from the linear onwards -/
  wW : ∀ n ∈ g.nodes.drop (T.k0 + 1), T.tW ∉ n.outs
  /-- linear output is not rewritten later -/
  wB : ∀ n ∈ g.nodes.drop (T.k0 + 2), T.tB ∉ n.outs
  /-- view output is not rewritten later -/
  wC : ∀ n ∈ g.nodes.drop (T.k0 + 3), T.tC ∉ n.outs

/-- The three node-literal facts, bundled. -/
structure BlockNodes (g : GraphDecl) (T : BlockTids) : Prop where
  hres : g.nodes[T.k0]? = some T.nReshape
  hlin : g.nodes[T.k0 + 1]? = some T.nLinear
  hview : g.nodes[T.k0 + 2]? = some T.nView

/-- Turn a `getElem?` fact into the `getElem` fact `reduce1/2` expect. -/
theorem getElem_of_getElem? {α : Type _} (l : List α) (i : Nat) (a : α)
    (h : l[i]? = some a) (hi : i < l.length) : l[i]'hi = a :=
  Option.some.inj (by rw [← List.getElem?_eq_getElem hi, h])

/-! ### 3. The parameterised block-level chained reduction lemma -/

/-- SPIKE CORE: one parameterised lemma giving the whole 3-node chained reduction
for an arbitrary graph `g` and an arbitrary block coordinate bundle `T`,
taking the packed side conditions `NW` and node facts `HN`. -/
theorem block_reduce3
    (g : GraphDecl) (init : Store) (T : BlockTids)
    (NW : BlockNotWritten g T) (HN : BlockNodes g T) :
    denoteGraphDistributedFaithful g init T.tA =
        fw_view (T.vhd :: T.vtl) (denoteGraphDistributedFaithful g init T.tIn) ∧
      denoteGraphDistributedFaithful g init T.tB =
        fw_linear (denoteGraphDistributedFaithful g init T.tA)
          (denoteGraphDistributedFaithful g init T.tW) ∧
      denoteGraphDistributedFaithful g init T.tC =
        fw_view (T.vhd :: T.vtl) (denoteGraphDistributedFaithful g init T.tB) := by
  have h0 : T.k0 < g.nodes.length := by have := NW.hlen; omega
  have h1 : T.k0 + 1 < g.nodes.length := by have := NW.hlen; omega
  have h2 : T.k0 + 2 < g.nodes.length := NW.hlen
  refine ⟨?_, ?_, ?_⟩
  · refine denoteGraphDistributedFaithful_reduce1 g init T.k0 T.nReshape
      T.tIn T.tA (fun x => fw_view (T.vhd :: T.vtl) x)
      h0 (getElem_of_getElem? _ _ _ HN.hres h0) ?_ NW.nil1 NW.wA NW.nil0 NW.wIn
    intro s
    unfold BlockTids.nReshape
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (show ("OpName.FW_reshape" : String) ≠ _ by decide)
      (show ("OpName.FW_reshape" : String) ≠ _ by decide)
      (show ("OpName.FW_reshape" : String) ≠ _ by decide)]
    exact applyNode_fw_reshape_out g s T.rank T.tIn T.tA (T.vhd :: T.vtl)
  · refine denoteGraphDistributedFaithful_reduce2 g init (T.k0 + 1) T.nLinear
      T.tA T.tW T.tB fw_linear
      h1 (getElem_of_getElem? _ _ _ HN.hlin h1) ?_ NW.nil2 NW.wB NW.nil1 NW.wA NW.wW
    intro s
    unfold BlockTids.nLinear
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (show ("OpName.FW_mix_precision_linear" : String) ≠ _ by decide)
      (show ("OpName.FW_mix_precision_linear" : String) ≠ _ by decide)
      (show ("OpName.FW_mix_precision_linear" : String) ≠ _ by decide)]
    exact applyNode_fw_mix_precision_linear_out_1p g s T.rank T.tA T.tW T.tB
  · refine denoteGraphDistributedFaithful_reduce1 g init (T.k0 + 2) T.nView
      T.tB T.tC (fun x => fw_view (T.vhd :: T.vtl) x)
      h2 (getElem_of_getElem? _ _ _ HN.hview h2) ?_ ?_ NW.wC NW.nil2 NW.wB
    · intro s
      unfold BlockTids.nView
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (show ("OpName.FW_view" : String) ≠ _ by decide)
        (show ("OpName.FW_view" : String) ≠ _ by decide)
        (show ("OpName.FW_view" : String) ≠ _ by decide)]
      exact applyNode_fw_view_out g s T.rank T.vhd T.vtl T.tB T.tC
    · exact NW.nil3

/-! ### 4. Instantiation with block 0 real data (SM nodes 507/508/509) -/

/-- Generic nonempty helper on the SM graph. -/
theorem sm_nonempty_drop (k : Nat) : ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

/-- Block 0 coordinates (from the real generated graph). -/
def blk0 : BlockTids :=
  { k0 := 507, rank := 0, tIn := 5348, tA := 5349, tW := 5350, tB := 5351,
    tC := 5352, vhd := 4096, vtl := [1024] }

theorem blk0_nodes : BlockNodes sm blk0 := by
  constructor <;> native_decide

theorem blk0_nw : BlockNotWritten sm blk0 where
  hlen := by native_decide
  nil0 := sm_nonempty_drop 507
  nil1 := sm_nonempty_drop 508
  nil2 := sm_nonempty_drop 509
  nil3 := sm_nonempty_drop 510
  wA := by native_decide +revert
  wIn := by native_decide +revert
  wW := by native_decide +revert
  wB := by native_decide +revert
  wC := by native_decide +revert

theorem blk0_chain (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5349 =
        fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5348) ∧
      denoteGraphDistributedFaithful sm initSM 5351 =
        fw_linear (denoteGraphDistributedFaithful sm initSM 5349)
          (denoteGraphDistributedFaithful sm initSM 5350) ∧
      denoteGraphDistributedFaithful sm initSM 5352 =
        fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5351) :=
  block_reduce3 sm initSM blk0 blk0_nw blk0_nodes

/-! ### 5. Instantiation with block 1 real data (SM nodes 542/543/544) -/

def blk1 : BlockTids :=
  { k0 := 542, rank := 0, tIn := 5397, tA := 5398, tW := 5399, tB := 5400,
    tC := 5401, vhd := 4096, vtl := [1024] }

theorem blk1_nodes : BlockNodes sm blk1 := by
  constructor <;> native_decide

theorem blk1_nw : BlockNotWritten sm blk1 where
  hlen := by native_decide
  nil0 := sm_nonempty_drop 542
  nil1 := sm_nonempty_drop 543
  nil2 := sm_nonempty_drop 544
  nil3 := sm_nonempty_drop 545
  wA := by native_decide +revert
  wIn := by native_decide +revert
  wW := by native_decide +revert
  wB := by native_decide +revert
  wC := by native_decide +revert

theorem blk1_chain (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5398 =
        fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5397) ∧
      denoteGraphDistributedFaithful sm initSM 5400 =
        fw_linear (denoteGraphDistributedFaithful sm initSM 5398)
          (denoteGraphDistributedFaithful sm initSM 5399) ∧
      denoteGraphDistributedFaithful sm initSM 5401 =
        fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5400) :=
  block_reduce3 sm initSM blk1 blk1_nw blk1_nodes

end
end TrainVerify.Denote.BlockParamSpike
