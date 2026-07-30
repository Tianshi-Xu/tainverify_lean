/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L23FaithfulExit
import denote.InnerChunkCEShard

/-!
# The loss head: the last two top-level goals on the faithful track

`goal_1` (tid `4673`, `losses`) and `goal_2` (tid `4674`, `z_losses`) are the two
outputs of the graph's final `FW_inner_chunk_ce`. Everything upstream of them is
already carried by `recon_goal_5930_faithful`, which hands over the trailing
RMSNorm as a `Gather2Rel`.

Both goals are **1-tp**: their single PM tensor product is the `AllGatherPrim`
node that the PM graph itself runs over the two per-rank cross-entropy outputs.
So the obligation is a plain value equality `SM t = PM t`, not a reconstruction.

The two sides differ in what they need:

* `4674` (`z_losses`) does not read the labels at all — `fw_inner_chunk_ce.snd`
  is `zScale * lse^2`. So the per-rank label chunk is irrelevant and the sharding
  argument goes through with no hypothesis beyond the standard five.
* `4673` (`losses`) reads `logits[l, y[l]]`, so it needs the caller-side
  well-formedness contract `hlabels : ∀ l < 4096, scalarToNat (valAt y l) < vocab`
  — the same contract `Pattern_1` states on the cut graph (AGENTS #29), carried
  here as an explicit parameter rather than an axiom. Non-vacuity is witnessed by
  `pattern_1_labels_hypothesis_witness`.
-/

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

/-! ### The five nodes of the head -/

def l23hdSmNorm : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [5928, 5929], outs := [5930] }

def l23hdSmCE : NodeDecl :=
  { rank := 0, op := "OpName.FW_inner_chunk_ce", ins := [5930, 5931, 4678],
    outs := [4673, 4674], params := [1024] }

def l23hdPmNorm0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [11727, 5929], outs := [11833] }

def l23hdPmNorm1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [11728, 5929], outs := [11834] }

def l23hdPmCE0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_inner_chunk_ce", ins := [11833, 5931, 11835],
    outs := [11837, 11839], params := [1024] }

def l23hdPmCE1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_inner_chunk_ce", ins := [11834, 5931, 11836],
    outs := [11838, 11840], params := [1024] }

def l23hdPmGatherFst : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [11837, 11838], outs := [4673],
    params := [0] }

def l23hdPmGatherSnd : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [11839, 11840], outs := [4674],
    params := [0] }

def l23hdPmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [4678], outs := [11835], params := [0] }

def l23hdPmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [4678], outs := [11836], params := [0] }

set_option maxRecDepth 1000000 in
theorem l23hd_sm_nodes :
    sm.nodes[925]'(by native_decide) = l23hdSmNorm ∧
    sm.nodes[926]'(by native_decide) = l23hdSmCE := by
  constructor <;> native_decide

set_option maxRecDepth 1000000 in
theorem l23hd_pm_nodes :
    pm.nodes[1914]'(by native_decide) = l23hdPmNorm0 ∧
    pm.nodes[1915]'(by native_decide) = l23hdPmNorm1 ∧
    pm.nodes[1916]'(by native_decide) = l23hdPmCE0 ∧
    pm.nodes[1917]'(by native_decide) = l23hdPmCE1 ∧
    pm.nodes[1918]'(by native_decide) = l23hdPmGatherFst ∧
    pm.nodes[1919]'(by native_decide) = l23hdPmGatherSnd ∧
    pm.nodes[12]'(by native_decide) = l23hdPmChunk0 ∧
    pm.nodes[25]'(by native_decide) = l23hdPmChunk1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

theorem l23hd_sm_nonempty (k : Nat) : ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] :=
  fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

theorem l23hd_pm_nonempty (k : Nat) : ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] :=
  fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

/-! ### Reducing the head nodes on the faithful evaluator -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem l23hd_red_sm5930 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5930 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 5928)
        (denoteGraphDistributedFaithful sm initSM 5929) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 925 l23hdSmNorm
    5928 5929 5930 fw_rms_norm
    (by native_decide) l23hd_sm_nodes.1 ?_
    (l23hd_sm_nonempty 926) (by native_decide)
    (l23hd_sm_nonempty 925) (by native_decide) (by native_decide)
  intro s
  unfold l23hdSmNorm
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out sm s 0 5928 5929 5930 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem l23hd_red_pm11833 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11833 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 11727)
        (denoteGraphDistributedFaithful pm initPM 5929) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1914 l23hdPmNorm0
    11727 5929 11833 fw_rms_norm
    (by native_decide) l23hd_pm_nodes.1 ?_
    (l23hd_pm_nonempty 1915) (by native_decide)
    (l23hd_pm_nonempty 1914) (by native_decide) (by native_decide)
  intro s
  unfold l23hdPmNorm0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out pm s 0 11727 5929 11833 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem l23hd_red_pm11834 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11834 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 11728)
        (denoteGraphDistributedFaithful pm initPM 5929) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1915 l23hdPmNorm1
    11728 5929 11834 fw_rms_norm
    (by native_decide) l23hd_pm_nodes.2.1 ?_
    (l23hd_pm_nonempty 1916) (by native_decide)
    (l23hd_pm_nonempty 1915) (by native_decide) (by native_decide)
  intro s
  unfold l23hdPmNorm1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out pm s 1 11728 5929 11834 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem l23hd_red_pm11835 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11835 =
      chunkPrimDimN 0 pm.numRanks 0 (denoteGraphDistributedFaithful pm initPM 4678) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 12 l23hdPmChunk0
    4678 11835 (fun x => chunkPrimDimN 0 pm.numRanks 0 x)
    (by native_decide) l23hd_pm_nodes.2.2.2.2.2.2.1 ?_
    (l23hd_pm_nonempty 13) (by native_decide)
    (l23hd_pm_nonempty 12) (by native_decide)
  intro s
  unfold l23hdPmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm s 0 4678 11835 0

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem l23hd_red_pm11836 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11836 =
      chunkPrimDimN 0 pm.numRanks 1 (denoteGraphDistributedFaithful pm initPM 4678) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 25 l23hdPmChunk1
    4678 11836 (fun x => chunkPrimDimN 0 pm.numRanks 1 x)
    (by native_decide) l23hd_pm_nodes.2.2.2.2.2.2.2 ?_
    (l23hd_pm_nonempty 26) (by native_decide)
    (l23hd_pm_nonempty 25) (by native_decide)
  intro s
  unfold l23hdPmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm s 1 4678 11836 0

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem l23hd_red_sm4674 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 4674 =
      (fw_inner_chunk_ce (denoteGraphDistributedFaithful sm initSM 5930)
        (denoteGraphDistributedFaithful sm initSM 5931)
        (denoteGraphDistributedFaithful sm initSM 4678)
        (((denoteGraphDistributedFaithful sm initSM 5931).shape.head?).getD 0)
        ((0 : Nat) : Scalar)).snd := by
  refine denoteGraphDistributedFaithful_reduce3 sm initSM 926 l23hdSmCE
    5930 5931 4678 4674
    (fun x w y => (fw_inner_chunk_ce x w y ((w.shape.head?).getD 0) ((0 : Nat) : Scalar)).snd)
    (by native_decide) l23hd_sm_nodes.2 ?_
    (l23hd_sm_nonempty 927) (by native_decide)
    (l23hd_sm_nonempty 926) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l23hdSmCE
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_inner_chunk_ce_snd_out_1p sm s 0 5930 5931 4678 4673 4674
    (by decide) (params := [1024])

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem l23hd_red_sm4673 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 4673 =
      (fw_inner_chunk_ce (denoteGraphDistributedFaithful sm initSM 5930)
        (denoteGraphDistributedFaithful sm initSM 5931)
        (denoteGraphDistributedFaithful sm initSM 4678)
        (((denoteGraphDistributedFaithful sm initSM 5931).shape.head?).getD 0)
        ((0 : Nat) : Scalar)).fst := by
  refine denoteGraphDistributedFaithful_reduce3 sm initSM 926 l23hdSmCE
    5930 5931 4678 4673
    (fun x w y => (fw_inner_chunk_ce x w y ((w.shape.head?).getD 0) ((0 : Nat) : Scalar)).fst)
    (by native_decide) l23hd_sm_nodes.2 ?_
    (l23hd_sm_nonempty 927) (by native_decide)
    (l23hd_sm_nonempty 926) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l23hdSmCE
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_inner_chunk_ce_fst_out_1p sm s 0 5930 5931 4678 4673 4674 [1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem l23hd_red_pm11839 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11839 =
      (fw_inner_chunk_ce (denoteGraphDistributedFaithful pm initPM 11833)
        (denoteGraphDistributedFaithful pm initPM 5931)
        (denoteGraphDistributedFaithful pm initPM 11835)
        (((denoteGraphDistributedFaithful pm initPM 5931).shape.head?).getD 0)
        ((0 : Nat) : Scalar)).snd := by
  refine denoteGraphDistributedFaithful_reduce3 pm initPM 1916 l23hdPmCE0
    11833 5931 11835 11839
    (fun x w y => (fw_inner_chunk_ce x w y ((w.shape.head?).getD 0) ((0 : Nat) : Scalar)).snd)
    (by native_decide) l23hd_pm_nodes.2.2.1 ?_
    (l23hd_pm_nonempty 1917) (by native_decide)
    (l23hd_pm_nonempty 1916) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l23hdPmCE0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_inner_chunk_ce_snd_out_1p pm s 0 11833 5931 11835 11837 11839
    (by decide) (params := [1024])

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem l23hd_red_pm11840 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11840 =
      (fw_inner_chunk_ce (denoteGraphDistributedFaithful pm initPM 11834)
        (denoteGraphDistributedFaithful pm initPM 5931)
        (denoteGraphDistributedFaithful pm initPM 11836)
        (((denoteGraphDistributedFaithful pm initPM 5931).shape.head?).getD 0)
        ((0 : Nat) : Scalar)).snd := by
  refine denoteGraphDistributedFaithful_reduce3 pm initPM 1917 l23hdPmCE1
    11834 5931 11836 11840
    (fun x w y => (fw_inner_chunk_ce x w y ((w.shape.head?).getD 0) ((0 : Nat) : Scalar)).snd)
    (by native_decide) l23hd_pm_nodes.2.2.2.1 ?_
    (l23hd_pm_nonempty 1918) (by native_decide)
    (l23hd_pm_nonempty 1917) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l23hdPmCE1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_inner_chunk_ce_snd_out_1p pm s 1 11834 5931 11836 11838 11840
    (by decide) (params := [1024])

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem l23hd_red_pm11837 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11837 =
      (fw_inner_chunk_ce (denoteGraphDistributedFaithful pm initPM 11833)
        (denoteGraphDistributedFaithful pm initPM 5931)
        (denoteGraphDistributedFaithful pm initPM 11835)
        (((denoteGraphDistributedFaithful pm initPM 5931).shape.head?).getD 0)
        ((0 : Nat) : Scalar)).fst := by
  refine denoteGraphDistributedFaithful_reduce3 pm initPM 1916 l23hdPmCE0
    11833 5931 11835 11837
    (fun x w y => (fw_inner_chunk_ce x w y ((w.shape.head?).getD 0) ((0 : Nat) : Scalar)).fst)
    (by native_decide) l23hd_pm_nodes.2.2.1 ?_
    (l23hd_pm_nonempty 1917) (by native_decide)
    (l23hd_pm_nonempty 1916) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l23hdPmCE0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_inner_chunk_ce_fst_out_1p pm s 0 11833 5931 11835 11837 11839 [1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem l23hd_red_pm11838 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11838 =
      (fw_inner_chunk_ce (denoteGraphDistributedFaithful pm initPM 11834)
        (denoteGraphDistributedFaithful pm initPM 5931)
        (denoteGraphDistributedFaithful pm initPM 11836)
        (((denoteGraphDistributedFaithful pm initPM 5931).shape.head?).getD 0)
        ((0 : Nat) : Scalar)).fst := by
  refine denoteGraphDistributedFaithful_reduce3 pm initPM 1917 l23hdPmCE1
    11834 5931 11836 11838
    (fun x w y => (fw_inner_chunk_ce x w y ((w.shape.head?).getD 0) ((0 : Nat) : Scalar)).fst)
    (by native_decide) l23hd_pm_nodes.2.2.2.1 ?_
    (l23hd_pm_nonempty 1918) (by native_decide)
    (l23hd_pm_nonempty 1917) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l23hdPmCE1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_inner_chunk_ce_fst_out_1p pm s 1 11834 5931 11836 11838 11840 [1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem l23hd_red_pm4674 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 4674 =
      allGatherPrimDimN 0 pm.numRanks 0
        [denoteGraphDistributedFaithful pm initPM 11839,
         denoteGraphDistributedFaithful pm initPM 11840] := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1919 l23hdPmGatherSnd
    11839 11840 4674
    (fun a b => allGatherPrimDimN 0 pm.numRanks 0 [a, b])
    (by native_decide) l23hd_pm_nodes.2.2.2.2.2.1 ?_
    (l23hd_pm_nonempty 1920) (by native_decide)
    (l23hd_pm_nonempty 1919) (by native_decide) (by native_decide)
  intro s
  unfold l23hdPmGatherSnd
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_allGatherPrimDimN_out pm s 0 [11839, 11840] 4674 0

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem l23hd_red_pm4673 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 4673 =
      allGatherPrimDimN 0 pm.numRanks 0
        [denoteGraphDistributedFaithful pm initPM 11837,
         denoteGraphDistributedFaithful pm initPM 11838] := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1918 l23hdPmGatherFst
    11837 11838 4673
    (fun a b => allGatherPrimDimN 0 pm.numRanks 0 [a, b])
    (by native_decide) l23hd_pm_nodes.2.2.2.2.1 ?_
    (l23hd_pm_nonempty 1919) (by native_decide)
    (l23hd_pm_nonempty 1918) (by native_decide) (by native_decide)
  intro s
  unfold l23hdPmGatherFst
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_allGatherPrimDimN_out pm s 0 [11837, 11838] 4673 0

/-! ### Graph inputs of the head

`5929` (the RMSNorm weight), `5931` (the vocabulary projection) and `4678` (the
labels) are init tids on both sides; the corresponding `initGoal`s say the two
graphs are handed the same tensor.
-/

set_option maxRecDepth 1000000 in
theorem l23hd_sm_input_fixed (W : Tid)
    (h : W = 5929 ∨ W = 5931 ∨ W = 4678) : ∀ n ∈ sm.nodes, W ∉ n.outs := by
  rcases h with rfl | rfl | rfl <;> native_decide

set_option maxRecDepth 1000000 in
theorem l23hd_pm_input_fixed (W : Tid)
    (h : W = 5929 ∨ W = 5931 ∨ W = 4678) : ∀ n ∈ pm.nodes, W ∉ n.outs := by
  rcases h with rfl | rfl | rfl <;> native_decide

set_option maxRecDepth 1000000 in
theorem l23hd_input_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (W : Tid) (g : LineageGoal) (hg : g ∈ initGoals)
    (htp : g.tps = [{rank := 0, tid := W}]) (hgd : g.gatherDim = 0)
    (hrep : g.replicated = false) (hts : g.ts = W)
    (hsw : ∀ n ∈ sm.nodes, W ∉ n.outs) (hpw : ∀ n ∈ pm.nodes, W ∉ n.outs) :
    denoteGraphDistributedFaithful sm initSM W =
      denoteGraphDistributedFaithful pm initPM W := by
  have h : initSM W = initPM W := by
    have hr := recon_weight initSM initPM hInit g hg W htp hgd hrep hts
    unfold denoteGraph at hr
    rw [foldl_applyNode_at_not_written sm sm.nodes initSM W hsw,
      foldl_applyNode_at_not_written pm pm.nodes initPM W hpw] at hr
    exact hr
  have e1 : denoteGraphDistributedFaithful sm initSM W = initSM W := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM W
      layer1_sm_nodes_nonempty hsw
  have e2 : denoteGraphDistributedFaithful pm initPM W = initPM W := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM W
      layer1_pm_nodes_nonempty hpw
  rw [e1, e2]; exact h

set_option maxRecDepth 1000000 in
theorem l23hd_pm_input_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) (W : Tid) (sh : Shape)
    (hmem : pmInitEnv W = some sh)
    (hpw : ∀ n ∈ pm.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm initPM W).shape = sh := by
  have e : denoteGraphDistributedFaithful pm initPM W = initPM W := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM W
      layer1_pm_nodes_nonempty hpw
  rw [e]; exact hPM W sh hmem

set_option maxRecDepth 1000000 in
theorem l23hd_w5929 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm initSM 5929 =
      denoteGraphDistributedFaithful pm initPM 5929 :=
  l23hd_input_eq initSM initPM hInit 5929 initGoal_5929 (by native_decide)
    rfl rfl rfl rfl (l23hd_sm_input_fixed 5929 (by decide))
    (l23hd_pm_input_fixed 5929 (by decide))

set_option maxRecDepth 1000000 in
theorem l23hd_w5931 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm initSM 5931 =
      denoteGraphDistributedFaithful pm initPM 5931 :=
  l23hd_input_eq initSM initPM hInit 5931 initGoal_5931 (by native_decide)
    rfl rfl rfl rfl (l23hd_sm_input_fixed 5931 (by decide))
    (l23hd_pm_input_fixed 5931 (by decide))

set_option maxRecDepth 1000000 in
theorem l23hd_w4678 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm initSM 4678 =
      denoteGraphDistributedFaithful pm initPM 4678 :=
  l23hd_input_eq initSM initPM hInit 4678 initGoal_4678 (by native_decide)
    rfl rfl rfl rfl (l23hd_sm_input_fixed 4678 (by decide))
    (l23hd_pm_input_fixed 4678 (by decide))

/-! ### The RMSNorm relation restated over the head's own tids

`recon_goal_5930_faithful` is stated over the collective expression, with the SM
weight on all three positions. Here it is re-expressed as the `Gather2Rel` between
the tids `5930` / `11833` / `11834` that the head nodes actually read.
-/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_goal_5930_faithful_tids (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2)
    (hx0 : (denoteGraphDistributedFaithful pm initPM 13257).shape.getD 0 0 = 2048) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm initSM 5930)
      (denoteGraphDistributedFaithful pm initPM 11833)
      (denoteGraphDistributedFaithful pm initPM 11834)
      [2048 * 2, 1024] [2048, 1024] := by
  have hrel := recon_goal_5930_faithful initSM initPM hSM hPM hInit hValues hCu hx0
  rw [l23hd_red_sm5930 initSM, l23hd_red_pm11833 initPM, l23hd_red_pm11834 initPM,
    ← l23hd_w5929 initSM initPM hInit]
  exact hrel

/-- Exact generated per-goal packaging for tid 5930. -/
theorem recon_intermediateGoal_5930_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2)
    (hx0 : (denoteGraphDistributedFaithful pm initPM 13257).shape.getD 0 0 = 2048) :
    InitGoalHolds pm.numRanks intermediateGoal_5930
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  change InitGoalHolds 2 intermediateGoal_5930
    (denoteGraphDistributedFaithful sm initSM)
    (denoteGraphDistributedFaithful pm initPM)
  exact Gather2Rel.to_initGoalHolds
    (denoteGraphDistributedFaithful sm initSM)
    (denoteGraphDistributedFaithful pm initPM) intermediateGoal_5930
    5930 11833 11834 [4096, 1024] [2048, 1024]
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (recon_goal_5930_faithful_tids initSM initPM hSM hPM hInit hValues hCu hx0)

/-- `.snd` (`z_losses = zScale * lse^2`) never reads the labels. -/
theorem l23hd_snd_y_independent
    (x w y y' : Tensor) (vocab : Nat) (zScale : Scalar) :
    (fw_inner_chunk_ce x w y vocab zScale).snd =
    (fw_inner_chunk_ce x w y' vocab zScale).snd := by
  unfold fw_inner_chunk_ce
  rfl


end

end TrainVerify.Denote.GeneratedPatterns
