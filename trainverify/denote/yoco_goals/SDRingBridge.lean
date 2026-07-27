/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.Layer0DistributedMigration

/-!
# Reaching the `_ringAttn` results that predate the first MoE

`denoteGraph_ringAttn` is not merely a bookkeeping variant of
`denoteGraphDistributed`: they differ at `FW_all2all_moe_gmm`, where the
distributed evaluator uses `applyNodeFullExpertMoE_value` and the ring evaluator
keeps `applyNode`'s historical per-rank reading. As `Denote.lean:21649` states,
the per-rank reading "is not the production interpretation" — every output token
can depend on every expert shard after dispatch and combine. Transporting a
`_ringAttn` conclusion past a MoE node would therefore import an unfaithful
semantics, so it is not done here.

Before the *first* MoE node the two agree, and
`denoteGraphDistributed_eq_ring_before_moe` supplies that equality. Composing it
with the region bridge reaches the faithful track for tids whose final writer
precedes SM 31 / PM 104.

The composite hypotheses stay decidable on the graph: a not-written fact and a
"prefix has no MoE" fact, both by `native_decide`.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated

noncomputable section

/-- Faithful = ring at an SM tid whose final writer precedes the first MoE. -/
theorem sd_sm_faithful_eq_ring (initSM : Store) (tid : Tid) (k : Nat) (hk : k ≤ 472)
    (hno : ∀ n ∈ sm.nodes.take k, n.op ≠ "OpName.FW_all2all_moe_gmm")
    (hwrite : ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs) :
    denoteGraphDistributedFaithful sm initSM tid = denoteGraph_ringAttn sm initSM tid := by
  rw [sd_sm_faithful_eq initSM tid k hk hwrite]
  exact denoteGraphDistributed_eq_ring_before_moe sm initSM tid k hno
    (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) hwrite

/-- Faithful = ring at a PM tid whose final writer precedes the first MoE. -/
theorem sd_pm_faithful_eq_ring (initPM : Store) (tid : Tid) (k : Nat) (hk : k ≤ 1003)
    (hno : ∀ n ∈ pm.nodes.take k, n.op ≠ "OpName.FW_all2all_moe_gmm")
    (hwrite : ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm initPM tid = denoteGraph_ringAttn pm initPM tid := by
  rw [sd_pm_faithful_eq initPM tid k hk hwrite]
  exact denoteGraphDistributed_eq_ring_before_moe pm initPM tid k hno
    (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) hwrite

end

end TrainVerify.Denote.GeneratedPatterns
