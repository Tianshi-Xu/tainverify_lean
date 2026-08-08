# YOCO CP-sharded K/V layout audit

## Finding

At the fixed revisions below, the CP-sharded K/V path is not equivalent to canonical causal attention when its input tensors already carry zigzag ownership.

- llm-train: `9a1be1d5fd1c063d80be82797692cdc7d23cfbef`
- nnScaler: `d3d468ed23edb2f28aa8566b2dfb6ed49c5955cf`

The wrapper gathers K/V in process-group rank order. `allgather_reducescatter` delegates directly to `all_gather`; it does not restore canonical token order. The zigzag kernel then passes physical K/V prefixes directly to FlashAttention.

Relevant fixed-source locations:

- `nnscaler/customized_ops/ring_attention/zigzag_allgather_attn_varlen.py:129-155`
- `nnscaler/runtime/adapter/nn.py:97-114`
- `nnscaler/customized_ops/ring_attention/core/zigzag_allgather_attn_varlen_implementation.py:96-125,236-270`

## Deterministic counterexample

For CP2 and sequence length 8, zigzag ownership is:

```text
rank0: [0,1,6,7]
rank1: [2,3,4,5]
```

Rank-order gather yields:

```text
[0,1,6,7,2,3,4,5]
```

For rank 1's front branch, the kernel uses the physical prefix of length 4:

```text
actual:   [0,1,6,7]
expected: [0,1,2,3]
```

With the asymmetric scalar K/V fixture in `scripts/audit_yoco_sharded_kv_layout.py`, real execution returned:

```json
{"absolute_error":28.02263293472279,"mismatch_reproduced":true,"reference_output":6.770023469101143,"wrapper_output":34.79265640382393}
```

Run:

```bash
python3 scripts/audit_yoco_sharded_kv_layout.py
```

## Existing-test coverage gap

The introducing nnScaler commit `a280599e4bb2d0beae5480baa11a27ec4d54f995` includes a real distributed numerical test, but that test slices K/V into ordinary contiguous halves before gathering. It does not pass K/V through the compiler-generated zigzag-owned ancestry seen by canonical L22. The wrapper-layout unit test checks that gather is called and checks shapes, but not token order. Thus neither test exercises the failing compiled layout.

A second independent CP2/L=4 experiment produced:

```text
canonical output:         [1.0, 1.622459, 2.629657, 4.343080]
rank-order gather output: [1.0, 4.5, 3.666667, 4.343080]
maximum absolute error:   2.8775406688
reordered positive control error: 0.0
```

## TrainVerify consequence

TrainVerify's faithful evaluator now models both graph contracts without hiding this discrepancy:

- shared buddy K/V TIDs use the legacy replicated-K/V path;
- distinct buddy K/V TIDs use rank-order sharded-K/V gather, matching the wrapper.

Canonical L22 has distinct K/V TIDs and genuine zigzag-sharded values. Therefore its full SM/PM attention equivalence is generally false at these fixed upstream revisions. No equality axiom, identity shuffle assumption, or caller-supplied computed relation may be used to close it.
