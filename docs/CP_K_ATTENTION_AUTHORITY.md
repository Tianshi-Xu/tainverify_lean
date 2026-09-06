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
PYTHONDONTWRITEBYTECODE=1 python -m pytest -q -p no:cacheprovider /home/v-zhouziyu/work/trainverify-cp-kattention-authority/scripts/tests/test_cp_k_attention_authority.py
```

## Remaining formal obligation

This source-derived oracle does **not** prove production-source/kernel equivalence.
A formal bridge still must connect pinned metadata/split/scatter and ordered
collectives to the complete Tensor-level global Denote operation, including
layout and group hypotheses. Row support and exact Real denominator/weighted-sum
lemmas can supply part of that bridge but are not by themselves its Tensor-level
lifting or a GPU implementation proof. Numerical agreement cannot replace those
obligations. No compiler or Lean semantics are changed by this artifact.
