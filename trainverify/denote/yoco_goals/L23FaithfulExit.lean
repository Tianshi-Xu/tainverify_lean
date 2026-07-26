/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L23FaithfulBlockTail
import denote.yoco_goals.ZigzagExitGear
import denote.yoco_goals.ZigzagExitCuBridge
import denote.yoco_goals.ZigzagExitCuAlias
import denote.yoco_goals.GatherOpGears

/-!
# The zigzag exit: closing `FW_maybe_unshuffle` back into an ordinary gather

This is the last goal of the zigzag region. Block 11's chain ends at `5926`
(SM 923, `FW_add`), which SM node 924 `FW_maybe_unshuffle` consumes to produce
`5928`. On the PM side nodes 1912/1913 run the genuine CP2 collective with
`params = [2,0]` and `[2,1]`.

The move is `Zigzag2Rel → Gather2Rel`: everything upstream of here is stated in
the zigzag layout, and `intermediateGoal_5928` is an ordinary dim-0 two-rank
goal, so the unshuffle is exactly the point where the two representations meet.

Two details that are easy to get wrong:

* **The SM side is degenerate.** SM 924 carries `params = [1,0]` and a singleton
  replica group, so its unshuffle is the identity on its data input — matching
  NNScaler's `cpSize = 1` early return. That is
  `applyNodeFaithfulUnshuffleValue_cpSize_one`.
* **Two different cu tids meet here.** The block-11 chain carries cu `5884`
  (`5345 + 49·11`), but node 924 reads cu `5927`, a separate init tid consumed
  only by the exit. `Zigzag2Rel.to_gather2_unshuffle` needs its `h` and
  `hdecoded` to mention the *same* tensor, so the alias
  `pm_cuseq_q_5884_eq_5927` is load-bearing, not cosmetic.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective
open TrainVerify.Denote.YOCInputValueClasses

noncomputable section

-- Naming the three unshuffle nodes. The reduction lemmas below need to rewrite
-- `replicaBuddies` at these nodes, and after `unfold applyNodeFaithfulUnshuffleValue`
-- the goal holds the record itself rather than `nodes[k]`. Inlining a record
-- literal whose fields contain lists into a lemma statement does not parse, so
-- follow `L12FaithfulMaybeShuffle` and give each node a name.

private def l23exSmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5926, 5927],
    outs := [5928], params := [1, 0] }

private def l23exPmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11721, 5927],
    outs := [11727], params := [2, 0] }

private def l23exPmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11722, 5927],
    outs := [11728], params := [2, 1] }

set_option maxRecDepth 1000000 in
private theorem l23ex_sm_node_facts :
    sm.nodes[924]'(by native_decide) = l23exSmUnshuffle := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l23ex_pm_node_facts :
    pm.nodes[1912]'(by native_decide) = l23exPmUnshuffle0 ∧
    pm.nodes[1913]'(by native_decide) = l23exPmUnshuffle1 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l23ex_pm_buddies :
    pm.replicaBuddies l23exPmUnshuffle0 =
      [l23exPmUnshuffle0, l23exPmUnshuffle1] := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l23ex_pm_buddies_r1 :
    pm.replicaBuddies l23exPmUnshuffle1 =
      [l23exPmUnshuffle0, l23exPmUnshuffle1] := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l23ex_sm_buddies :
    sm.replicaBuddies l23exSmUnshuffle = [l23exSmUnshuffle] := by
  native_decide

-- Both cu tids meeting at the exit are graph inputs: no PM node writes either.
set_option maxRecDepth 1000000 in
private theorem l23ex_cu_not_written : ∀ n ∈ pm.nodes, (5927 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l23ex_cu5884_not_written : ∀ n ∈ pm.nodes, (5884 : Tid) ∉ n.outs := by
  native_decide

-- Prefix/suffix facts for reducing the two PM unshuffle nodes. Every (k, tid)
-- pair below was checked against the generated graph before being written here:
-- no node at index >= k writes tid.
set_option maxRecDepth 1000000 in
private theorem l23ex_pm_nonempty (k : Nat) : ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l23ex_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1913, 11727), (1914, 11728), (1912, 11721), (1912, 11722),
                     (1912, 5927), (1913, 11721), (1913, 11722), (1913, 5927)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

-- Reduce each PM unshuffle node to the collective expression that
-- `recon_goal_5928_faithful` speaks about, so the relation can be restated over
-- the tids `11727` / `11728` that `intermediateGoal_5928` names.
set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23ex_red_pm11727 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11727 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 11721,
         denoteGraphDistributedFaithful pm initPM 11722]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5927)) 2 0 := by
  refine denoteGraphDistributedFaithful_reduce3 pm initPM 1912 l23exPmUnshuffle0
    11721 11722 5927 11727
    (fun a b cu => fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0)
    (by native_decide) l23ex_pm_node_facts.1 ?_
    (l23ex_pm_nonempty 1913) (l23ex_pm_not_written 1913 11727 (by decide))
    (l23ex_pm_nonempty 1912) (l23ex_pm_not_written 1912 11721 (by decide))
    (l23ex_pm_not_written 1912 11722 (by decide))
    (l23ex_pm_not_written 1912 5927 (by decide))
  intro st
  unfold l23exPmUnshuffle0
  rw [applyNodeDistributedFaithful_unshuffle_out]
  unfold applyNodeFaithfulUnshuffleValue
  rw [show pm.replicaBuddies
    { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11721, 5927],
      outs := [11727], params := [2, 0] } =
      [l23exPmUnshuffle0, l23exPmUnshuffle1] from l23ex_pm_buddies]
  unfold l23exPmUnshuffle0 l23exPmUnshuffle1
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23ex_red_pm11728 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11728 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 11721,
         denoteGraphDistributedFaithful pm initPM 11722]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5927)) 2 1 := by
  refine denoteGraphDistributedFaithful_reduce3 pm initPM 1913 l23exPmUnshuffle1
    11721 11722 5927 11728
    (fun a b cu => fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1)
    (by native_decide) l23ex_pm_node_facts.2 ?_
    (l23ex_pm_nonempty 1914) (l23ex_pm_not_written 1914 11728 (by decide))
    (l23ex_pm_nonempty 1913) (l23ex_pm_not_written 1913 11721 (by decide))
    (l23ex_pm_not_written 1913 11722 (by decide))
    (l23ex_pm_not_written 1913 5927 (by decide))
  intro st
  unfold l23exPmUnshuffle1
  rw [applyNodeDistributedFaithful_unshuffle_out]
  unfold applyNodeFaithfulUnshuffleValue
  rw [show pm.replicaBuddies
    { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11722, 5927],
      outs := [11728], params := [2, 1] } =
      [l23exPmUnshuffle0, l23exPmUnshuffle1] from l23ex_pm_buddies_r1]
  unfold l23exPmUnshuffle0 l23exPmUnshuffle1
  rfl

/-! ### The closure

`recon_goal_5928_faithful` is the last obligation of the zigzag region. Note the
hypothesis list: the five standard arguments carried by every faithful theorem,
plus `hx0`.

`hx0` states that rank 0's zigzag metadata tensor has leading dimension 2048. It
is *not* derivable from the other hypotheses: `ZigzagCuWF.local_tokens` relates
that dimension to `listLast! cu`, but pinning either one to a concrete number
needs an external fact about the workload. It is the same kind of caller-side
well-formedness contract as `hCu` itself (AGENTS #29), so it is stated as an
explicit parameter rather than smuggled in as an axiom — the trust sits with the
caller that supplies the graph, and is visible in the signature.
-/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_goal_5928_faithful (initSM initPM : Store)
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
      (denoteGraphDistributedFaithful sm initSM 5928)
      (fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 11721,
         denoteGraphDistributedFaithful pm initPM 11722]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5927)) 2 0)
      (fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 11721,
         denoteGraphDistributedFaithful pm initPM 11722]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5927)) 2 1)
      [2048 * 2, 1024] [2048, 1024] := by
  -- Block 11's chain reaches 5926 carrying cu 5884; the exit node reads 5927.
  have hrel := recon_zigzagGoal_5926_faithful initSM initPM hSM hPM hInit hValues hCu
  have hcu : denoteGraphDistributedFaithful pm initPM 5884 =
      denoteGraphDistributedFaithful pm initPM 5927 := by
    have e5884 : denoteGraphDistributedFaithful pm initPM 5884 = initPM 5884 := by
      unfold denoteGraphDistributedFaithful
      exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5884
        layer1_pm_nodes_nonempty l23ex_cu5884_not_written
    have e5927 : denoteGraphDistributedFaithful pm initPM 5927 = initPM 5927 := by
      unfold denoteGraphDistributedFaithful
      exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5927
        layer1_pm_nodes_nonempty l23ex_cu_not_written
    rw [e5884, e5927]
    exact pm_cuseq_q_5884_eq_5927 initPM hValues.2
  rw [hcu] at hrel
  -- `hdecoded` at the exit tid, from the caller-side well-formedness contract.
  have hdec : decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5927) =
      [0, 2 * 2048] :=
    decodeCuSeqlens_pm_5927 initPM hPM hValues.2 hCu hx0
  exact Zigzag2Rel.to_gather2_unshuffle 2048 1024 hrel (by decide) (by decide)
    (by decide) hdec

-- The exit output stated over the tids `intermediateGoal_5928` names, rather than
-- over the collective expression.
set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_goal_5928_faithful_tids (initSM initPM : Store)
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
      (denoteGraphDistributedFaithful sm initSM 5928)
      (denoteGraphDistributedFaithful pm initPM 11727)
      (denoteGraphDistributedFaithful pm initPM 11728)
      [2048 * 2, 1024] [2048, 1024] := by
  rw [l23ex_red_pm11727 initPM, l23ex_red_pm11728 initPM]
  exact recon_goal_5928_faithful initSM initPM hSM hPM hInit hValues hCu hx0

/-! ### Past the exit: the trailing RMSNorm

`5930` sits after `FW_maybe_unshuffle`, in ordinary dim-0 gather territory. It is
the first consumer of the closure and the last goal of this neighbourhood.
-/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_goal_5930_faithful (initSM initPM : Store)
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
      (fw_rms_norm (denoteGraphDistributedFaithful sm initSM 5928)
        (denoteGraphDistributedFaithful sm initSM 5929))
      (fw_rms_norm (denoteGraphDistributedFaithful pm initPM 11727)
        (denoteGraphDistributedFaithful sm initSM 5929))
      (fw_rms_norm (denoteGraphDistributedFaithful pm initPM 11728)
        (denoteGraphDistributedFaithful sm initSM 5929))
      [2048 * 2, 1024] [2048, 1024] :=
  Gather2Rel.rms_norm 2048 1024
    (recon_goal_5928_faithful_tids initSM initPM hSM hPM hInit hValues hCu hx0)
    (by decide) (by decide)

end

end TrainVerify.Denote.GeneratedPatterns
