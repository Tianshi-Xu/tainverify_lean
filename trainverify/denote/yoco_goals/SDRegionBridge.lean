/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.FaithfulDistributedBridge
import denote.yoco_goals.Layer1DistributedMigration

/-!
# Region-level form of the faithful/distributed bridge

`denote_faithful_eq_distributed_of_prefix` needs three facts per use. Two of them
do not actually depend on the tid, and one does not depend on the cutoff either,
so they can be discharged once for the whole self-decoder region instead of once
per goal:

* **node outputs are nonempty** — a global property of both graphs, already
  proved as `layer1_sm_nodes_nonempty` / `layer1_pm_nodes_nonempty`;
* **the prefix is collective-free** — the three divergent operators first appear
  at SM 472 and PM 1003, so *any* `take k` with `k ≤ 472` (resp. `1003`) is
  clean. Proving it at the boundary and restricting downwards covers every
  cutoff.

What remains per goal is the genuine obligation: after its final writer, nothing
writes the tid again. That one is decided by `native_decide` on the graph.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated

noncomputable section

set_option maxRecDepth 1000000 in
private theorem sd_sm_clean_472 : ∀ n ∈ sm.nodes.take 472,
    n.op ≠ "OpName.FW_maybe_shuffle" ∧
    n.op ≠ "OpName.FW_maybe_unshuffle" ∧
    n.op ≠ "OpName.FW_attn_zigzag" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sd_pm_clean_1003 : ∀ n ∈ pm.nodes.take 1003,
    n.op ≠ "OpName.FW_maybe_shuffle" ∧
    n.op ≠ "OpName.FW_maybe_unshuffle" ∧
    n.op ≠ "OpName.FW_attn_zigzag" := by
  native_decide

/-- Any prefix inside the self-decoder region is collective-free. -/
theorem sd_sm_clean (k : Nat) (hk : k ≤ 472) : ∀ n ∈ sm.nodes.take k,
    n.op ≠ "OpName.FW_maybe_shuffle" ∧
    n.op ≠ "OpName.FW_maybe_unshuffle" ∧
    n.op ≠ "OpName.FW_attn_zigzag" := by
  intro n hn
  exact sd_sm_clean_472 n ((List.take_prefix_take_left hk).subset hn)

/-- Any prefix inside the self-decoder region is collective-free (PM side). -/
theorem sd_pm_clean (k : Nat) (hk : k ≤ 1003) : ∀ n ∈ pm.nodes.take k,
    n.op ≠ "OpName.FW_maybe_shuffle" ∧
    n.op ≠ "OpName.FW_maybe_unshuffle" ∧
    n.op ≠ "OpName.FW_attn_zigzag" := by
  intro n hn
  exact sd_pm_clean_1003 n ((List.take_prefix_take_left hk).subset hn)

/-- Faithful = distributed at any self-decoder tid, given only the per-tid
not-written fact. -/
theorem sd_sm_faithful_eq (initSM : Store) (tid : Tid) (k : Nat) (hk : k ≤ 472)
    (hwrite : ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs) :
    denoteGraphDistributedFaithful sm initSM tid =
      denoteGraphDistributed sm initSM tid :=
  denote_faithful_eq_distributed_of_prefix sm initSM tid k
    (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn))
    hwrite (sd_sm_clean k hk)

/-- Faithful = distributed at any self-decoder tid (PM side). -/
theorem sd_pm_faithful_eq (initPM : Store) (tid : Tid) (k : Nat) (hk : k ≤ 1003)
    (hwrite : ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm initPM tid =
      denoteGraphDistributed pm initPM tid :=
  denote_faithful_eq_distributed_of_prefix pm initPM tid k
    (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn))
    hwrite (sd_pm_clean k hk)

end

end TrainVerify.Denote.GeneratedPatterns
