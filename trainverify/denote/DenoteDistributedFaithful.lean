/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.ZigzagCollective

/-!
# Graph-aware faithful distributed denotation

This evaluator composes the existing distributed evaluator (including its faithful
full-expert MoE and graph-aware ring-attention branches) with the value-faithful
cross-rank semantics for forward `maybe_shuffle`, `maybe_unshuffle`, and zigzag
attention.

Replica order is exactly `GraphDecl.replicaBuddies`; it is never inferred or sorted.
Shuffle inputs have order `[data, cu_seqlens]` and parameters `[cpSize, cpRank]`.
Zigzag attention inputs are `[Q, K, V, cuQ, cuKV]` with parameters
`[qHeads, kvHeads, qDim, vDim, causal, window]`; graph rank count and node rank supply
its CP coordinates. Missing replica metadata inherits the existing fail-closed
singleton behavior of `replicaBuddies`.
-/

open TrainVerify.Denote.ZigzagCollective

namespace TrainVerify.Denote
noncomputable section

/-- Cross-rank value of a generated forward maybe-shuffle node. -/
noncomputable def applyNodeFaithfulShuffleValue
    (g : GraphDecl) (s : Store) (n : NodeDecl) : Tensor :=
  let buddies := g.replicaBuddies n
  let dataShards := buddies.map (fun m => s (m.ins.getD 0 0))
  let cu := decodeCuSeqlens (s (n.ins.getD 1 0))
  fw_maybe_shuffle_collective dataShards cu
    (n.params.getD 0 1) (n.params.getD 1 0)

/-- Cross-rank value of a generated forward maybe-unshuffle node. -/
noncomputable def applyNodeFaithfulUnshuffleValue
    (g : GraphDecl) (s : Store) (n : NodeDecl) : Tensor :=
  let buddies := g.replicaBuddies n
  let dataShards := buddies.map (fun m => s (m.ins.getD 0 0))
  let cu := decodeCuSeqlens (s (n.ins.getD 1 0))
  fw_maybe_unshuffle_collective dataShards cu
    (n.params.getD 0 1) (n.params.getD 1 0)

/-- Cross-rank value of a generated forward zigzag-attention node.  Only Q is
collected from ordered replica buddies; K/V and both cu tensors are node-local,
matching the Python wrapper's already-replicated K/V contract. -/
noncomputable def applyNodeFaithfulZigzagAttnValue
    (g : GraphDecl) (s : Store) (n : NodeDecl) : Tensor :=
  let buddies := g.replicaBuddies n
  let qShards := buddies.map (fun m => s (m.ins.getD 0 0))
  fw_attn_zigzag_collective qShards
    (s (n.ins.getD 1 0)) (s (n.ins.getD 2 0))
    (s (n.ins.getD 3 0)) (s (n.ins.getD 4 0))
    (n.params.getD 0 0) (n.params.getD 1 0)
    (n.params.getD 2 0) (n.params.getD 3 0)
    (decide (n.params.getD 4 0 ≠ 0)) (n.params.getD 5 0)
    g.numRanks n.rank

/-- Store one collective value at every output declared by the node. -/
noncomputable def storeCollectiveOutputs
    (s : Store) (n : NodeDecl) (value : Tensor) : Store :=
  storeSet s (n.outs.map fun tid => (tid, value))

/-- Faithful distributed apply step. Forward shuffle/unshuffle are intercepted;
all other operators delegate *exactly* to `applyNodeDistributed`. -/
noncomputable def applyNodeDistributedFaithful
    (g : GraphDecl) (s : Store) (n : NodeDecl) : Store :=
  if n.op = "OpName.FW_maybe_shuffle" then
    storeCollectiveOutputs s n (applyNodeFaithfulShuffleValue g s n)
  else if n.op = "OpName.FW_maybe_unshuffle" then
    storeCollectiveOutputs s n (applyNodeFaithfulUnshuffleValue g s n)
  else if n.op = "OpName.FW_attn_zigzag" then
    storeCollectiveOutputs s n (applyNodeFaithfulZigzagAttnValue g s n)
  else
    applyNodeDistributed g s n

/-- Production graph fold using the faithful distributed node evaluator. -/
noncomputable def denoteGraphDistributedFaithful
    (g : GraphDecl) (init : Store) : Store :=
  g.nodes.foldl (applyNodeDistributedFaithful g) init

/-- Faithful lineage statement over the production distributed evaluator with an
explicit caller-side input contract.  The contract is a hypothesis, not an axiom:
generated YOCO goals use it for label-domain bounds and packed-sequence
well-formedness that are runtime preconditions rather than graph-derived facts. -/
def CoarseLineageHoldsWithInitDistributedFaithfulWithContract
    (sm pm : GraphDecl) (goal : LineageGoal)
    (smInit pmInit : ShapeEnv) (initGoals : List LineageGoal)
    (inputContract : Store → Store → Prop) : Prop :=
  ∀ (initSM initPM : Store),
    StoreShapesHold initSM smInit →
    StoreShapesHold initPM pmInit →
    InitGoalsHold pm.numRanks initGoals initSM initPM →
    inputContract initSM initPM →
    let smStore := denoteGraphDistributedFaithful sm initSM
    let pmStore := denoteGraphDistributedFaithful pm initPM
    let ts := smStore goal.ts
    let tps := goal.tps.map (fun p => pmStore p.tid)
    ts.shape = goal.tsShape ∧
      (tps.map (fun t => t.shape)) = goal.tpShapes ∧
      ts = reconstructForGoal goal pm.numRanks tps

/-- Faithful lineage statement without additional runtime preconditions. -/
def CoarseLineageHoldsWithInitDistributedFaithful
    (sm pm : GraphDecl) (goal : LineageGoal)
    (smInit pmInit : ShapeEnv) (initGoals : List LineageGoal) : Prop :=
  CoarseLineageHoldsWithInitDistributedFaithfulWithContract
    sm pm goal smInit pmInit initGoals (fun _ _ => True)

/-- A generated singleton-output shuffle writes its collective result. -/
theorem applyNodeDistributedFaithful_shuffle_out
    (g : GraphDecl) (s : Store) (rank : Nat)
    (dataTid cuTid outTid : Tid) (params : List Nat) :
    applyNodeDistributedFaithful g s
      { rank := rank, op := "OpName.FW_maybe_shuffle",
        ins := [dataTid, cuTid], outs := [outTid], params := params } outTid =
      applyNodeFaithfulShuffleValue g s
        { rank := rank, op := "OpName.FW_maybe_shuffle",
          ins := [dataTid, cuTid], outs := [outTid], params := params } := by
  unfold applyNodeDistributedFaithful storeCollectiveOutputs
  simp [storeSet]

/-- A generated singleton-output unshuffle writes its collective result. -/
theorem applyNodeDistributedFaithful_unshuffle_out
    (g : GraphDecl) (s : Store) (rank : Nat)
    (dataTid cuTid outTid : Tid) (params : List Nat) :
    applyNodeDistributedFaithful g s
      { rank := rank, op := "OpName.FW_maybe_unshuffle",
        ins := [dataTid, cuTid], outs := [outTid], params := params } outTid =
      applyNodeFaithfulUnshuffleValue g s
        { rank := rank, op := "OpName.FW_maybe_unshuffle",
          ins := [dataTid, cuTid], outs := [outTid], params := params } := by
  unfold applyNodeDistributedFaithful storeCollectiveOutputs
  simp [storeSet]

/-- A generated singleton-output zigzag-attention node writes its faithful value. -/
theorem applyNodeDistributedFaithful_zigzag_attn_out
    (g : GraphDecl) (s : Store) (rank : Nat)
    (qTid kTid vTid cuQTid cuKVTid outTid : Tid) (params : List Nat) :
    applyNodeDistributedFaithful g s
      { rank := rank, op := "OpName.FW_attn_zigzag",
        ins := [qTid, kTid, vTid, cuQTid, cuKVTid], outs := [outTid],
        params := params } outTid =
      applyNodeFaithfulZigzagAttnValue g s
        { rank := rank, op := "OpName.FW_attn_zigzag",
          ins := [qTid, kTid, vTid, cuQTid, cuKVTid], outs := [outTid],
          params := params } := by
  unfold applyNodeDistributedFaithful storeCollectiveOutputs
  simp [storeSet]

/-- The extension is conservative away from its three forward collectives. -/
theorem applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
    (g : GraphDecl) (s : Store) (n : NodeDecl)
    (hshuffle : n.op ≠ "OpName.FW_maybe_shuffle")
    (hunshuffle : n.op ≠ "OpName.FW_maybe_unshuffle")
    (hattn : n.op ≠ "OpName.FW_attn_zigzag" := by decide) :
    applyNodeDistributedFaithful g s n = applyNodeDistributed g s n := by
  unfold applyNodeDistributedFaithful
  rw [if_neg hshuffle, if_neg hunshuffle, if_neg hattn]

/-- A faithful step cannot change a tensor id which is not one of the node's
outputs.  The nonempty-output premise is inherited from the distributed evaluator's
fail-closed `getD` handling; every generated graph node satisfies it. -/
theorem applyNodeDistributedFaithful_eq_of_not_mem_outs
    (g : GraphDecl) (s : Store) (n : NodeDecl) (tid : Tid)
    (hnil : n.outs ≠ []) (h : tid ∉ n.outs) :
    applyNodeDistributedFaithful g s n tid = s tid := by
  unfold applyNodeDistributedFaithful
  by_cases hshuffle : n.op = "OpName.FW_maybe_shuffle"
  · rw [if_pos hshuffle]
    unfold storeCollectiveOutputs
    apply storeSet_eq_of_not_mem_fst
    simpa using h
  · rw [if_neg hshuffle]
    by_cases hunshuffle : n.op = "OpName.FW_maybe_unshuffle"
    · rw [if_pos hunshuffle]
      unfold storeCollectiveOutputs
      apply storeSet_eq_of_not_mem_fst
      simpa using h
    · rw [if_neg hunshuffle]
      by_cases hattn : n.op = "OpName.FW_attn_zigzag"
      · rw [if_pos hattn]
        unfold storeCollectiveOutputs
        apply storeSet_eq_of_not_mem_fst
        simpa using h
      · rw [if_neg hattn]
        unfold applyNodeDistributed
        by_cases hmoe : n.op = "OpName.FW_all2all_moe_gmm"
        · rw [if_pos hmoe]
          have hmem : n.outs.getD 0 0 ∈ n.outs := by
            cases hout : n.outs with
            | nil => exact absurd hout hnil
            | cons a rest => rw [List.getD_cons_zero]; exact List.mem_cons_self
          have hneq : tid ≠ n.outs.getD 0 0 := by
            intro heq
            exact h (heq ▸ hmem)
          apply storeSet_eq_of_not_mem_fst
          simpa using hneq
        · rw [if_neg hmoe]
          exact applyNodeRingAttn_skip g s n tid hnil h

/-- Folding faithful steps preserves an id that no remaining node writes. -/
theorem foldl_applyNodeDistributedFaithful_at_not_written
    (g : GraphDecl) (nodes : List NodeDecl) (s : Store) (tid : Tid)
    (hnil : ∀ n ∈ nodes, n.outs ≠ [])
    (hwrite : ∀ n ∈ nodes, tid ∉ n.outs) :
    (nodes.foldl (applyNodeDistributedFaithful g) s) tid = s tid := by
  induction nodes generalizing s with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.foldl]
    rw [ih]
    · exact applyNodeDistributedFaithful_eq_of_not_mem_outs g s a tid
        (hnil a List.mem_cons_self) (hwrite a List.mem_cons_self)
    · intro n hn
      exact hnil n (List.mem_cons_of_mem a hn)
    · intro n hn
      exact hwrite n (List.mem_cons_of_mem a hn)

/-- The previous distributed fold has the same read-preservation property. -/
theorem foldl_applyNodeDistributed_at_not_written
    (g : GraphDecl) (nodes : List NodeDecl) (s : Store) (tid : Tid)
    (hnil : ∀ n ∈ nodes, n.outs ≠ [])
    (hwrite : ∀ n ∈ nodes, tid ∉ n.outs) :
    (nodes.foldl (applyNodeDistributed g) s) tid = s tid := by
  induction nodes generalizing s with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.foldl]
    rw [ih]
    · unfold applyNodeDistributed
      by_cases hmoe : a.op = "OpName.FW_all2all_moe_gmm"
      · rw [if_pos hmoe]
        have hmem : a.outs.getD 0 0 ∈ a.outs := by
          cases hout : a.outs with
          | nil => exact absurd hout (hnil a List.mem_cons_self)
          | cons x xs => rw [List.getD_cons_zero]; exact List.mem_cons_self
        have hneq : tid ≠ a.outs.getD 0 0 := by
          intro heq
          exact hwrite a List.mem_cons_self (heq ▸ hmem)
        apply storeSet_eq_of_not_mem_fst
        simpa using hneq
      · rw [if_neg hmoe]
        exact applyNodeRingAttn_skip g s a tid
          (hnil a List.mem_cons_self) (hwrite a List.mem_cons_self)
    · intro n hn
      exact hnil n (List.mem_cons_of_mem a hn)
    · intro n hn
      exact hwrite n (List.mem_cons_of_mem a hn)

/-- On a collective-free list, the faithful and previous distributed folds agree
extensionally, for every initial store. -/
theorem foldl_applyNodeDistributedFaithful_eq_applyNodeDistributed
    (g : GraphDecl) (nodes : List NodeDecl) (s : Store)
    (hops : ∀ n ∈ nodes,
      n.op ≠ "OpName.FW_maybe_shuffle" ∧
      n.op ≠ "OpName.FW_maybe_unshuffle" ∧
      n.op ≠ "OpName.FW_attn_zigzag") :
    nodes.foldl (applyNodeDistributedFaithful g) s =
      nodes.foldl (applyNodeDistributed g) s := by
  induction nodes generalizing s with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.foldl]
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      g s a (hops a List.mem_cons_self).1 (hops a List.mem_cons_self).2.1
        (hops a List.mem_cons_self).2.2]
    apply ih
    intro n hn
    exact hops n (List.mem_cons_of_mem a hn)

/-- Prefix form of conservative compatibility. -/
theorem foldl_take_applyNodeDistributedFaithful_eq_applyNodeDistributed
    (g : GraphDecl) (nodes : List NodeDecl) (s : Store) (k : Nat)
    (hops : ∀ n ∈ nodes.take k,
      n.op ≠ "OpName.FW_maybe_shuffle" ∧
      n.op ≠ "OpName.FW_maybe_unshuffle" ∧
      n.op ≠ "OpName.FW_attn_zigzag") :
    (nodes.take k).foldl (applyNodeDistributedFaithful g) s =
      (nodes.take k).foldl (applyNodeDistributed g) s :=
  foldl_applyNodeDistributedFaithful_eq_applyNodeDistributed g (nodes.take k) s hops

/-- Read an id from a faithful full-graph denotation at any prefix after its final
writer. -/
theorem denoteGraphDistributedFaithful_eq_prefix
    (g : GraphDecl) (init : Store) (tid : Tid) (k : Nat)
    (hnil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hwrite : ∀ n ∈ g.nodes.drop k, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid =
      ((g.nodes.take k).foldl (applyNodeDistributedFaithful g) init) tid := by
  unfold denoteGraphDistributedFaithful
  have hsplit : g.nodes.take k ++ g.nodes.drop k = g.nodes :=
    List.take_append_drop k g.nodes
  calc
    (g.nodes.foldl (applyNodeDistributedFaithful g) init) tid =
        ((g.nodes.take k ++ g.nodes.drop k).foldl
          (applyNodeDistributedFaithful g) init) tid := by rw [hsplit]
    _ = ((g.nodes.take k).foldl (applyNodeDistributedFaithful g) init) tid := by
      rw [List.foldl_append]
      exact foldl_applyNodeDistributedFaithful_at_not_written g _ _ tid hnil hwrite

/-- Expose one faithful node whose output is not overwritten by the suffix. -/
theorem denoteGraphDistributedFaithful_node_core
    (g : GraphDecl) (init : Store) (k : Nat) (node : NodeDecl) (outTid : Tid)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (hnil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hwrite : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs) :
    denoteGraphDistributedFaithful g init outTid =
      applyNodeDistributedFaithful g
        ((g.nodes.take k).foldl (applyNodeDistributedFaithful g) init) node outTid := by
  rw [denoteGraphDistributedFaithful_eq_prefix g init outTid (k + 1) hnil hwrite]
  have hstep := congrFun
    (foldl_take_succ (applyNodeDistributedFaithful g) g.nodes init k hk) outTid
  rw [hstep, hnode]

/-- Read an input of node `k` from the final faithful denotation when that node and
suffix do not write it. -/
theorem denoteGraphDistributedFaithful_prefix_read
    (g : GraphDecl) (init : Store) (k : Nat) (tid : Tid)
    (hnil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hwrite : ∀ n ∈ g.nodes.drop k, tid ∉ n.outs) :
    ((g.nodes.take k).foldl (applyNodeDistributedFaithful g) init) tid =
      denoteGraphDistributedFaithful g init tid :=
  (denoteGraphDistributedFaithful_eq_prefix g init tid k hnil hwrite).symm

/-- Reduce a faithful node whose local output equation has one store read. -/
theorem denoteGraphDistributedFaithful_reduce1
    (g : GraphDecl) (init : Store) (k : Nat) (node : NodeDecl)
    (in0 outTid : Tid) (opfun : Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (happly : ∀ s, applyNodeDistributedFaithful g s node outTid = opfun (s in0))
    (hafterNil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hafterWrite : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpreNil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre0 : ∀ n ∈ g.nodes.drop k, in0 ∉ n.outs) :
    denoteGraphDistributedFaithful g init outTid =
      opfun (denoteGraphDistributedFaithful g init in0) := by
  rw [denoteGraphDistributedFaithful_node_core g init k node outTid hk hnode
      hafterNil hafterWrite,
    happly,
    denoteGraphDistributedFaithful_prefix_read g init k in0 hpreNil hpre0]

/-- Reduce a faithful node whose local output equation has two store reads. -/
theorem denoteGraphDistributedFaithful_reduce2
    (g : GraphDecl) (init : Store) (k : Nat) (node : NodeDecl)
    (in0 in1 outTid : Tid) (opfun : Tensor → Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (happly : ∀ s, applyNodeDistributedFaithful g s node outTid =
      opfun (s in0) (s in1))
    (hafterNil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hafterWrite : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpreNil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre0 : ∀ n ∈ g.nodes.drop k, in0 ∉ n.outs)
    (hpre1 : ∀ n ∈ g.nodes.drop k, in1 ∉ n.outs) :
    denoteGraphDistributedFaithful g init outTid =
      opfun (denoteGraphDistributedFaithful g init in0)
        (denoteGraphDistributedFaithful g init in1) := by
  rw [denoteGraphDistributedFaithful_node_core g init k node outTid hk hnode
      hafterNil hafterWrite,
    happly,
    denoteGraphDistributedFaithful_prefix_read g init k in0 hpreNil hpre0,
    denoteGraphDistributedFaithful_prefix_read g init k in1 hpreNil hpre1]

/-- Reduce a faithful node whose local output equation has three store reads. -/
theorem denoteGraphDistributedFaithful_reduce3
    (g : GraphDecl) (init : Store) (k : Nat) (node : NodeDecl)
    (in0 in1 in2 outTid : Tid) (opfun : Tensor → Tensor → Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (happly : ∀ s, applyNodeDistributedFaithful g s node outTid =
      opfun (s in0) (s in1) (s in2))
    (hafterNil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hafterWrite : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpreNil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre0 : ∀ n ∈ g.nodes.drop k, in0 ∉ n.outs)
    (hpre1 : ∀ n ∈ g.nodes.drop k, in1 ∉ n.outs)
    (hpre2 : ∀ n ∈ g.nodes.drop k, in2 ∉ n.outs) :
    denoteGraphDistributedFaithful g init outTid =
      opfun (denoteGraphDistributedFaithful g init in0)
        (denoteGraphDistributedFaithful g init in1)
        (denoteGraphDistributedFaithful g init in2) := by
  rw [denoteGraphDistributedFaithful_node_core g init k node outTid hk hnode
      hafterNil hafterWrite,
    happly,
    denoteGraphDistributedFaithful_prefix_read g init k in0 hpreNil hpre0,
    denoteGraphDistributedFaithful_prefix_read g init k in1 hpreNil hpre1,
    denoteGraphDistributedFaithful_prefix_read g init k in2 hpreNil hpre2]

/-- Previous-distributed counterpart of the faithful prefix read theorem. -/
theorem denoteGraphDistributed_eq_prefix
    (g : GraphDecl) (init : Store) (tid : Tid) (k : Nat)
    (hnil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hwrite : ∀ n ∈ g.nodes.drop k, tid ∉ n.outs) :
    denoteGraphDistributed g init tid =
      ((g.nodes.take k).foldl (applyNodeDistributed g) init) tid := by
  unfold denoteGraphDistributed
  have hsplit : g.nodes.take k ++ g.nodes.drop k = g.nodes :=
    List.take_append_drop k g.nodes
  calc
    (g.nodes.foldl (applyNodeDistributed g) init) tid =
        ((g.nodes.take k ++ g.nodes.drop k).foldl
          (applyNodeDistributed g) init) tid := by rw [hsplit]
    _ = ((g.nodes.take k).foldl (applyNodeDistributed g) init) tid := by
      rw [List.foldl_append]
      exact foldl_applyNodeDistributed_at_not_written g _ _ tid hnil hwrite

/-- Bridge to the previous distributed denotation for any id whose relevant prefix
precedes the first faithful collective and which is not rewritten afterwards. -/
theorem denoteGraphDistributedFaithful_eq_distributed_of_prefix
    (g : GraphDecl) (init : Store) (tid : Tid) (k : Nat)
    (hops : ∀ n ∈ g.nodes.take k,
      n.op ≠ "OpName.FW_maybe_shuffle" ∧
      n.op ≠ "OpName.FW_maybe_unshuffle" ∧
      n.op ≠ "OpName.FW_attn_zigzag")
    (hnil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hwrite : ∀ n ∈ g.nodes.drop k, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid =
      denoteGraphDistributed g init tid := by
  rw [denoteGraphDistributedFaithful_eq_prefix g init tid k hnil hwrite]
  rw [foldl_take_applyNodeDistributedFaithful_eq_applyNodeDistributed g g.nodes init k hops]
  exact (denoteGraphDistributed_eq_prefix g init tid k hnil hwrite).symm

/-- With a singleton replica group and generated `[1, 0]` parameters, shuffle
collapses extensionally to the node's data input. -/
theorem applyNodeFaithfulShuffleValue_cpSize_one
    (g : GraphDecl) (s : Store) (n : NodeDecl)
    (hbuddy : g.replicaBuddies n = [n])
    (hcp : n.params.getD 0 1 = 1)
    (hrank : n.params.getD 1 0 = 0) :
    applyNodeFaithfulShuffleValue g s n = s (n.ins.getD 0 0) := by
  unfold applyNodeFaithfulShuffleValue
  rw [hbuddy]
  simp only [List.map]
  rw [hcp, hrank]
  exact fw_maybe_shuffle_collective_cpSize_one _ _ _ rfl

/-- Mirror of `applyNodeFaithfulShuffleValue_cpSize_one` for the unshuffle side.
The single-machine graph's `FW_maybe_unshuffle` (generated node 924) carries
`params = [1, 0]` and a singleton replica group, so the collective degenerates to
the identity on its data input — matching the Python early-return branch for
`cpSize = 1`. -/
theorem applyNodeFaithfulUnshuffleValue_cpSize_one
    (g : GraphDecl) (s : Store) (n : NodeDecl)
    (hbuddy : g.replicaBuddies n = [n])
    (hcp : n.params.getD 0 1 = 1)
    (hrank : n.params.getD 1 0 = 0) :
    applyNodeFaithfulUnshuffleValue g s n = s (n.ins.getD 0 0) := by
  unfold applyNodeFaithfulUnshuffleValue
  rw [hbuddy]
  simp only [List.map]
  rw [hcp, hrank]
  exact fw_maybe_unshuffle_collective_cpSize_one _ _ _ rfl

end
end TrainVerify.Denote
