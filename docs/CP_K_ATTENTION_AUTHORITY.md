# CP-K forward attention: source-derived numerical authority

## Pinned sources

Inspected with `git show <revision>:<path>`, not by importing the working copy:

- nnScaler **`d3d468ed23edb2f28aa8566b2dfb6ed49c5955cf`** at
  `/home/v-zhouziyu/work/trainverify/.hermes-runs/remote-yoco-release-20260822/upstream/nnscaler`.
  Paths below are relative to that repository:
  - `nnscaler/customized_ops/ring_attention/zigzag_allgather_attn_varlen.py:129–137`:
    ordinary sharded K/V gathered on dimension zero, only within `process_group`,
    when `cp_sharded_kv and not kv_is_gathered`.
  - Same file `:215–242`: emitted CP group may be a contiguous **subgroup** of
    the plan; `rank` below must be **group-local**, not a physical device ID.
  - `nnscaler/runtime/adapter/collectives.py:71–85`: all-gather concatenates
    the process-group-rank-ordered tensor list. This is not zigzag restoration.
  - `nnscaler/customized_ops/ring_attention/varlen_utils.py:90–127`: the actual
    single-sequence rank-to-position map.
  - `nnscaler/customized_ops/ring_attention/core/zigzag_allgather_attn_varlen_implementation.py`:
    `_build_branch_cu_seqlens`, `_build_q_split_indices`, metadata `:85–99`, and
    two branch calls/output scatter `:236–279`.
- llm-train **`9a1be1d5fd1c063d80be82797692cdc7d23cfbef`** at the sibling
  `/home/v-zhouziyu/work/trainverify/.hermes-runs/remote-yoco-release-20260822/upstream/llm-train`:
  `llm/arch/attention.py:170–210` selects this cross-attention wrapper, passes
  `causal=True`, and sets `cp_sharded_kv=True`; pre-gather is a separate flag.
- FlashAttention's documented **2.1+ bottom-right causal convention** is an
  explicit dependency assumption, not established by the nnScaler Git pin.
  Inspected [v2.5.9 README, “2.1: Change behavior of causal flag”](https://github.com/Dao-AILab/flash-attention/blob/v2.5.9/README.md#21-change-behavior-of-causal-flag):
  `seqlen_q=2, seqlen_k=5` keeps `[0,1,2,3]`, then `[0,1,2,3,4]`.
  This does **not** assert which FlashAttention version is installed.

Global comparison is the single-head specialization of
`trainverify/denote/Denote.lean:1445–1549` (`attnScale`, `attnMaskedAt`,
`fw_attn_varlen`) and the Q-unshuffle/gather → global attention →
chunk/shuffle dataflow in `trainverify/denote/ZigzagCollective.lean:168–189`,
read at TrainVerify `410847df804255aae60b88088d7f008e792063f1`.

## Exact single-sequence formulas

Write `P` for CP size (the task's K), `L=2s>0` for local Q length,
`N=P*L`, and `0≤r<P`. Q/K/V global sequence lengths all equal N, with
`cuQ=cuK=[0,N]`; hence `kv_extra_lens=0`.

- Rank r Q positions, in local output order:
  `[r*s, …, (r+1)*s-1] ++ [(2P-r-1)*s, …, (2P-r)*s-1]`.
- Ordinary K/V shard r owns `[r*L, …, (r+1)*L-1]`.
  Rank-order gather therefore yields logical global order `[0,…,N-1]`.
- Front prefix length `F=(r+1)*s`; end prefix length `E=(2P-r)*s`.
- Both branch Q cumulative lengths are `[0,s,s]` (length entries `[s,0]`).
  K cumulative lengths are `[0,F,N]` / `[0,E,N]`: the unused suffix is a
  **second segment with zero Q rows**, not extra keys in the active segment.
- Front local Q indices are `[0,…,s-1]`; end indices `[s,…,2s-1]`.
  Source scatters each branch output back into those local slots.
- For branch prefix length B and query index `a<s`, bottom-right masking keeps
  `0≤j<B` and `j≤a+B-s`. Front gives global query `i=r*s+a`;
  end gives `i=(2P-r-1)*s+a`. In both cases the allowed set is exactly `0,…,i`.
- For every allowed j, logit is `dot(Q[i],K[j])/sqrt(head_dim)`; output is
  `sum_j exp(logit_j)*V[j] / sum_j exp(logit_j)`. Thus the row's key set,
  logits, denominator, and value numerator coincide with global causal attention
  under these assumptions. The executable model uses Python floats and unshifted
  exponentials like Denote's formula, not GPU rounding or fused softmax.

## Supported scope and evidence

The test file `scripts/tests/test_cp_k_attention_authority.py` is self-contained:
its numerical routines use Python stdlib only; **pytest is the test runner**.
It does not import nnScaler, Torch, FlashAttention, or execute Lean/GPU kernels.
Helpers assume the stated domain; this is not a runtime validation API.

Restricted equivalence domain: positive even local length, single sequence,
equal Q/K/V lengths, zigzag Q, ordinary dimension-zero-sharded K/V with identical
ordered CP membership, causal=true, **Denote window=0 ↔ source `(-1,-1)`**,
**dropout=0, default softmax scale, no ALiBi**. The scalar fixtures cover one Q/KV
head and two V channels; they do not constitute multi-head/GQA test coverage.
No packed sequences, KV extras, replicated/mixed KV, alternate windows,
noncausal mode, backward, LSE/auxiliary consumption, or Cute-backend validation.
Graph rank count/order must match this one CP group; subgroup/CP×EP graph
adapters require separate authority, not an inference from shapes.

The focused suite has **26 tests**, CP sizes **3 and 5**, local lengths **2,4,6**,
all ranks. Position-identifying asymmetric Q/K and unique two-channel V detect:

1. Exact cumulative-length/index formulas and bottom-right/global support.
2. Source front/end output versus canonical attention at the **same rank's
   global Q positions**, never a contiguous output chunk by mistake.
3. Wrong zigzag K/V gather and reversed ordinary KV buddy order.
4. Missing Q restoration on the global Denote dataflow, with explicit restoration
   as the positive control.
5. Noncausal counterexamples: source still restricts front/end prefixes while
   global noncausal attention uses all N keys. Therefore noncausal mode must be
   rejected by the proposed equivalence/compiler domain, not silently admitted.

Observed maximum causal error was **0.0** for these scalar computations.
For CP3/L4 the wrong-KV, reversed-KV, and missing-Q-restoration errors were
`62.62756831007564`, `111.23969928918231`, `4.618663184577798`.
Noncausal rank-zero errors at L4 were `55.6364137002412` (CP3) and
`148.50692812535866` (CP5). These are finite numerical witnesses, not universal
proofs. Metadata and numerical tests were observed RED before their respective
implementations, then GREEN. In-memory removal of each of the three layout
perturbations separately made its negative-control assertion RED; no mutation
was retained on disk.

Run (add `-s` for concrete ownership arrays, V values, outputs, and errors):

```sh
PYTHONDONTWRITEBYTECODE=1 python -m pytest -q -p no:cacheprovider scripts/tests/test_cp_k_attention_authority.py
```

## Evidence boundary

This source-derived oracle does **not** prove production-source/kernel equivalence.
The Lean Tensor lifting below proves the hand-translated Real front/end model
against the existing global Denote operation. The compiler extension below binds
graph groups, metadata and writer operands; connecting a new captured runtime's
parameter defaults to that restricted contract remains a source-authority
obligation. GPU floating-point behavior and the installed FlashAttention
backend/version are not proved. The existing Lean operator semantics are unchanged.

## Kernel-checked foundation

Four new leaf modules make the two evidence tracks explicit:

- `denote.ZigzagKAttention`: `ShardedRel.attention_chunks` reconstructs full
  tensors from the actual ordered chunks; `ZigzagKRel.attn_zigzag_sharded_kv_single`
  carries complete shape/value relations through the existing global attention
  collective for every positive K, including its K=1 branch. The mathematical
  theorem permits separate unrestricted `cuKV`; this is **not** permission to
  widen the restricted equal-length, shared-metadata source domain above.
- `denote.ZigzagKAttentionWitness`: assumption-free, nonconstant CP3 Q/K/V,
  Q-heads=2 and KV-heads=1, establish entry, attention output, and ordinary exit
  reconstruction of the actual full `fw_attn_varlen` tensor. These are collective
  relation witnesses, not generated graph/public certificates.
- `denote.ZigzagKAttentionSource`: proves causal-prefix denominator equality and
  weighted-row equality, retaining Denote's zero-denominator branch. Its
  `front_row_eq` / `end_row_eq` incorporate bottom-right offset; the separate
  `fw_attn_varlen_row` connects the scalar row to actual Denote flat-index,
  head, channel and logit expressions.
- `denote.ZigzagKAttentionSourceWitness`: actual nonconstant CP3 GQA front/end
  rows plus CP5 conditional row callers. This does not establish that source
  Q extraction/scatter and a generated graph supply those same tensor rows.

Parent `lake build` materialized all four `.olean` files. All 20 public theorem
axiom groups are exactly the standard `propext`, `Classical.choice`, `Quot.sound`;
no `sorryAx`, native decision or source-refinement axiom is used. The parent
re-ran all 26 scalar tests. Independently removing the source oracle's
bottom-right offset and reversing its actual K gather each rejected all six
CP-size/local-length positive cases. No mutation is retained.

## Tensor lifting of the source-derived Real model

The follow-up adds four leaf modules:

- `ZigzagKAttentionRows`: closed-form single-sequence `zigzagPos`, logical-row
  bounds, and `ZigzagKRel.full_row_spec/full_row_value`. These derive actual
  `qs.getD rank` values, both tensor shapes and all flat-index bounds from the
  existing relation, preserving the head and channel coordinates.
- `ZigzagKAttentionTensor`: `sourceOutput` computes the two source-derived
  branches using **local Q**, front/end K prefixes, bottom-right causal offsets,
  the existing GQA head map and scatter into local output slots. Dot-product
  transport and a coordinate form of `fw_attn_varlen_row` connect the local
  computation to global attention without changing either existing operation.
- `ZigzagKAttentionRefinement`: `ZigzagKRel.sourceOutput_eq_collective` proves
  complete Tensor equality between that source model using **actual ordered K/V
  gathers** and `fw_attn_zigzag_collective_sharded_kv`. Every Q-row equality is
  derived internally from `ZigzagKRel`, never supplied by the caller. This
  theorem uses shared single-sequence metadata, K>1, positive dimensions and
  query-head divisibility by KV heads, and fixes causal/no-window/default-scale
  mathematics. Source dropout and ALiBi are absent from this restricted model.
- `ZigzagKAttentionRefinementWitness`: the same concrete CP3 GQA inputs prove
  each rank, complete ordered Tensor-list equality, and ordinary exit
  reconstruction of the source-model attention outputs.

All four modules build, and all 12 additional public theorem axiom sets are
subsets of kernel3. Together with the first foundation this is eight leaf
modules and 32 audited public theorems. A standalone exact-source assembly of
Tensor+Refinement compiles and materializes an `.olean` without importing their
production `.olean` files. Coherently shifting either the front or end prefix in
both the source definition and its observation lemma makes that assembly fail
in the unchanged refinement proof; neither negative creates an `.olean`.
A separate wrong-Q-row probe timed out and is **not** counted as a semantic
negative receipt.

## Shared compiler and exact graph evidence

The dedicated `KRankAttentionCertificate` and `k_attention_renderer` now bind
entry's internal `zigzag_k` Q and independent ordinary external K/V facts to the
actual attention output, then exit and public gather. All three projections reuse
one shared three-segment DAG. The compiler checks SM1/PMK>=3, positive/even local
length, six matching attention parameters, valid GQA, shared external cu,
entry-derived packed/value-class authority and explicit ordered replica groups.
CP2 keeps its previous path; no source subgroup or new backward path is admitted.

The renderer revalidates exact graph/producers, restores Q/K/V roles from the
typed certificate rather than sorted pre-facts, retains full frame/no-clobber
obligations, and consumes the source Tensor refinement for each PM writer. The
six graph parameters do not encode dropout, explicit scale or ALiBi. Those
remain the restricted Real operator interpretation above; no nonexistent Node
fields or new runtime/source capture are asserted.

`cp_k_attention_witness.witness_source()` generates the committed exact CP3
`fixtures/CPKAttentionFW.lean`: nonconstant Q[12,2,2], K[12,1,2], V[12,1,3],
execution order [2,0,1] but semantic ranks [0,1,2], shared metadata90/91.
Its `prove_goal_0_closed` proves full output shape, all shard shapes and complete
reconstruction. `publicInputs` inhabits the actual public contract independently;
`inhabitedPublicOutput` applies that exact theorem. No intermediate Q/attention
InitGoal is introduced. CP5 `conditional_source(5)` separately compiles the same
three graph segments with its initial-state hypothesis, not a CP5 inhabited
public theorem. Both exact outputs materialize `.olean`; generated proofs retain
the existing native-decision baseline, while publicInputs is kernel3.

Parent validation passes 213 focused attention/entry/exit/prefix/import-policy
tests, including committed-fixture byte reproduction. Causal/window/GQA guard removal
is detected independently; renderer packed/alias/cross liveness and region-alias
guard removals are detected. Exact graph-only variants with wrong attention buddy
order, cross-buddy Q clobber and retained-Q clobber are all rejected by Lean and
produce no `.olean`. Full-model builds/canonical regeneration were not rerun for
this incremental slice; no publication artifacts changed. Packed multi-sequence,
BW attention, additional KV layouts, source subgroup composition and new real
configuration captures remain separate work.
