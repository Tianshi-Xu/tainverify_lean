#!/usr/bin/env python3
"""Deterministic CP2 counterexample for rank-order gathering zigzag K/V shards.

This mirrors the fixed nnScaler wrapper contract: CP-sharded K/V are gathered in
process-group rank order, while the kernel consumes physical prefixes selected by
its causal branch metadata.  No GPU or third-party package is required.
"""
from __future__ import annotations

import json
import math


def scalar_attention(ids: list[int], keys: list[float], values: list[float]) -> float:
    weights = [math.exp(keys[i]) for i in ids]
    normalizer = sum(weights)
    return sum(w * values[i] for w, i in zip(weights, ids)) / normalizer


def main() -> None:
    # CP2, sequence length 8. Zigzag owners are rank0=[0,1,6,7], rank1=[2,3,4,5].
    rank0 = [0, 1, 6, 7]
    rank1 = [2, 3, 4, 5]
    rank_order_gather = rank0 + rank1

    # For rank=1, slice_size=2, the wrapper kernel's front branch uses
    # front_k_len=(rank+1)*slice_size=4 and therefore the physical prefix.
    wrapper_key_ids = rank_order_gather[:4]
    reference_key_ids = [0, 1, 2, 3]
    keys = [-2.0, -0.5, 0.7, 1.5, 2.1, -1.3, 3.0, -2.7]
    values = [0.0, 1.0, 4.0, 9.0, 16.0, 25.0, 36.0, 49.0]
    wrapper_output = scalar_attention(wrapper_key_ids, keys, values)
    reference_output = scalar_attention(reference_key_ids, keys, values)
    error = abs(wrapper_output - reference_output)

    report = {
        "cp_size": 2,
        "sequence_length": 8,
        "rank0_zigzag_owner_ids": rank0,
        "rank1_zigzag_owner_ids": rank1,
        "rank_order_gather": rank_order_gather,
        "rank1_front_wrapper_key_ids": wrapper_key_ids,
        "rank1_front_reference_key_ids": reference_key_ids,
        "wrapper_output": wrapper_output,
        "reference_output": reference_output,
        "absolute_error": error,
        "mismatch_reproduced": error > 1e-12,
    }
    print(json.dumps(report, sort_keys=True))
    if not report["mismatch_reproduced"]:
        raise SystemExit("expected the sharded-K/V layout mismatch to reproduce")


if __name__ == "__main__":
    main()
