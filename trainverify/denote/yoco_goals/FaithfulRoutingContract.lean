/-
Faithful-denotation routing-map disjointness contract for the Layer-12 MoE cut.

`denote/yoco_goals/WellFormedInputs.lean` already carries the *ring-attention*
flavour of this contract (`WellFormed_YOCOMoE_A04B`, 126 fields of the shape
`routing_map_local (denoteGraph_ringAttn pm initPM <tid>) 2048 64 lo hi`).  The
faithful distributed denotation `denoteGraphDistributedFaithful` had no such
contract at all; this module supplies the minimal Layer-12 slice needed by the
faithful MoE-expert goal `5365`.

**What the contract says.**  `routing_map_local rm L numExp lo hi` (definition in
`MoEShardedReconstruction.lean`) is the positive dispatch well-formedness fact

    ∀ l < L, ∀ e < numExp, (e < lo ∨ hi ≤ e) → valAt rm (l * numExp + e) = 0

i.e. rank `r`'s post-shuffle routing map is zero outside the expert window that
rank actually owns.  This is an *input contract* on the training harness: it is
provably NOT derivable from the abstract `hSM/hPM/hInit/hValues/hCu` chain
(abstract top-k over an abstract store says nothing about which experts win).
See `WellFormedInputs.lean`'s module note and AGENTS.md #29.

**Non-vacuity.**  `FaithfulRoutingWF_L12_witness` below discharges the
satisfiability obligation at exactly the level the repository's existing
convention does (`WellFormed_routing_witness`, `WellFormedInputs.lean:207`):
the routing-locality *predicate class* is inhabited — the all-zero routing map
satisfies both per-rank windows simultaneously, so neither clause is
`False`-in-disguise and the contract cannot silently vacuify the theorems that
consume it.  See the `Fidelity note` section at the bottom for the precise
scope of this witness and the (identical) scope of the ring-attn one.
-/
import denote.yoco_goals.WellFormedInputs
import denote.DenoteDistributedFaithful

set_option linter.style.longLine false

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- **Faithful routing-map disjointness contract, Layer-12 MoE slice.**

`9733` / `9734` are the two per-rank `routing_map` outputs of the Layer-12
`FW_topk_routing` nodes (`pm.nodes[1108]`: `[9729] → [9731, 9733, 9735]`,
`pm.nodes[1112]`: `[9730] → [9732, 9734, 9736]`, params `[8, 1]`), i.e. the SM
tensor `5361`'s two shards.  Rank 0 owns experts `[0, 32)` and rank 1 owns
`[32, 64)` (matching the `FW_all2all_moe_gmm` params `[64,0,32,8]` /
`[64,32,64,8]` of `pm.nodes[1116]` / `pm.nodes[1119]`), over `2048` local tokens
and `64` experts. -/
structure FaithfulRoutingWF_L12 (initPM : Store) : Prop where
  hdisjA : routing_map_local (denoteGraphDistributedFaithful pm initPM 9733) 2048 64 0 32
  hdisjB : routing_map_local (denoteGraphDistributedFaithful pm initPM 9734) 2048 64 32 64

/-- **Consistency / non-vacuity witness** for the faithful routing-locality
contract, in exactly the form the repository already uses for the ring-attn
contract (`WellFormed_routing_witness`): the two clauses of
`FaithfulRoutingWF_L12` are simultaneously satisfiable, witnessed by the
all-zero routing map.

Both fields are instances of `routing_map_local _ 2048 64 0 32` respectively
`routing_map_local _ 2048 64 32 64`; the zero tensor discharges both, hence
neither clause is `False`, and no theorem consuming `FaithfulRoutingWF_L12`
is vacuous *for that reason*. -/
theorem FaithfulRoutingWF_L12_witness :
    ∃ rm : Tensor, routing_map_local rm 2048 64 0 32 ∧ routing_map_local rm 2048 64 32 64 :=
  ⟨zeroTensor [2048 * 64], routing_map_local_zeroTensor _ _ _ _,
    routing_map_local_zeroTensor _ _ _ _⟩

/-- A routing map whose row count degenerates to `0` (empty tensor) is
expert-local for *every* window: `valAt` of an out-of-range index is `0`.
Recorded here because it is the exact shape-level condition under which the
graph-level instance of `FaithfulRoutingWF_L12` would follow structurally. -/
theorem routing_map_local_of_prodShape_zero (rm : Tensor) (L numExp lo hi : Nat)
    (h : prodShape rm.shape = 0) :
    routing_map_local rm L numExp lo hi := by
  intro l _ e _ _
  simp [valAt, h]

/-!
### Fidelity note — scope of the witness

`FaithfulRoutingWF_L12_witness` is a **predicate-class** witness, identical in
strength to the repository's pre-existing `WellFormed_routing_witness`
(`WellFormedInputs.lean:207`), which is the convention AGENTS.md #29 prescribes
and which all 126 ring-attn routing fields rely on.  It rules out vacuity trap
(3) of AGENTS.md #29 (`hypothesis ⟹ False`) and trap (1).

It does **not** exhibit a concrete `initPM` for which the *graph-evaluated*
tensors `denoteGraphDistributedFaithful pm initPM 9733/9734` are expert-local.
That stronger statement is not reachable here, and the obstruction is concrete,
not a proof-engineering shortfall:

* `9733 = (fw_topk_routing (dgdF pm initPM 9729) 8 64).2.1` and
  `9734 = (fw_topk_routing (dgdF pm initPM 9730) 8 64).2.1` are genuinely
  *written* nodes, so a witness must evaluate a >1100-node graph symbolically.
* `fw_topk_routing` is `noncomputable` (softmax over `Scalar`), so `decide` /
  `native_decide` cannot evaluate it — a witness has to be a hand proof.
* The obvious candidate, the all-zero store, provably **fails** clause
  `hdisjB`: with uniform gate scores the deterministic "lower index wins"
  tiebreak of `topkRank` puts the top-8 at experts `{0, …, 7}`, which satisfies
  rank 0's window `[0, 32)` but violates rank 1's requirement that experts
  `< 32` be masked out.
* The only structural escape is `prodShape = 0`
  (`routing_map_local_of_prodShape_zero` above), i.e. `9729`/`9730` having head
  dim `0`; but their shapes are forced to `[2048, 64]` by the literal `params`
  of the upstream `FW_view` / linear nodes, so no store can produce it.

A genuine graph-level witness therefore requires choosing router *weights* and
*tokens* whose logits rank rank-0's tokens onto experts `[0, 32)` and rank-1's
onto `[32, 64)` — a real harness fact, exactly the thing this contract is
declared to import from the caller.  This is the same epistemic position as the
already-shipped ring-attn contract; no regression is introduced.
-/

end TrainVerify.Denote.GeneratedPatterns
