"""CPU scalar oracle derived from pinned source, not a production/GPU test.

See docs/CP_K_ATTENTION_AUTHORITY.md for source and domain authority.
Only the test runner requires pytest; the numerical model uses the stdlib.
"""

from math import exp, sqrt

import pytest

NNSCALER_REV = "d3d468ed23edb2f28aa8566b2dfb6ed49c5955cf"
LLM_TRAIN_REV = "9a1be1d5fd1c063d80be82797692cdc7d23cfbef"


def max_error(actual, expected):
    assert len(actual) == len(expected)
    assert all(len(a) == len(b) for a, b in zip(actual, expected))
    return max(abs(x - y) for a, b in zip(actual, expected) for x, y in zip(a, b))


@pytest.mark.parametrize("cp", [3, 5])
@pytest.mark.parametrize("local", [2, 4, 6])
def test_bottom_right_support_equals_global_support(cp, local):
    half = local // 2
    all_positions = []
    for rank in range(cp):
        owned = positions(cp, local, rank)
        all_positions.extend(owned)
        cuq, front, end, _, _ = branch_metadata(cp, local, rank)
        for branch, cuk in enumerate((front, end)):
            for a in range(half):
                allowed = [j for j in range(cuk[1]) if j <= a + cuk[1] - cuq[1]]
                assert allowed == list(range(owned[branch * half + a] + 1))
    assert sorted(all_positions) == list(range(cp * local))


@pytest.mark.parametrize("cp", [3, 5])
@pytest.mark.parametrize("local", [2, 4, 6])
def test_layout_negative_controls_and_q_restoration(cp, local):
    q, k, v = fixture(cp, local)
    ownership = [positions(cp, local, r) for r in range(cp)]
    q_shards = [[q[i] for i in ids] for ids in ownership]
    ks = [k[r * local:(r + 1) * local] for r in range(cp)]
    vs = [v[r * local:(r + 1) * local] for r in range(cp)]
    full = canonical(q, k, v)
    expected = [full[i] for ids in ownership for i in ids]
    correct = [row for shard in source_front_end(q_shards, ks, vs) for row in shard]
    assert max_error(correct, expected) < 1e-12

    # Wrong physical K/V ownership: treat ordinary K/V as if zigzag-sharded.
    zigzag_k = [[k[i] for i in ids] for ids in ownership]
    zigzag_v = [[v[i] for i in ids] for ids in ownership]
    wrong_kv = [row for shard in source_front_end(q_shards, zigzag_k, zigzag_v)
                for row in shard]
    # A separate ordered-buddy fault swaps entire ordinary K/V shards.
    reverse_kv = [row for shard in source_front_end(q_shards, ks[::-1], vs[::-1])
                  for row in shard]

    gathered_q = [row for shard in q_shards for row in shard]
    # Wrong Denote path: omit Q unshuffle, but retain output chunk/shuffle.
    missing_restore_full = canonical(gathered_q, k, v)
    missing_restore = [missing_restore_full[i] for ids in ownership for i in ids]
    restored_q = [[] for _ in q]
    for ids, shard in zip(ownership, q_shards):
        for i, row in zip(ids, shard):
            restored_q[i] = row
    restored_full = canonical(restored_q, k, v)
    restored = [restored_full[i] for ids in ownership for i in ids]
    assert max_error(restored, expected) < 1e-12
    assert max_error(wrong_kv, expected) > 1e-3
    assert max_error(reverse_kv, expected) > 1e-3
    assert max_error(missing_restore, expected) > 1e-3
    print({"cp": cp, "local": local, "Q_positions": ownership,
           "ordinary_KV_gather": list(range(cp * local)),
           "wrong_KV_gather": [i for ids in ownership for i in ids],
           "V_first_channel": [row[0] for row in v],
           "source_rank0": correct[:local], "canonical_rank0": expected[:local],
           "max_error": max_error(correct, expected),
           "wrong_KV_error": max_error(wrong_kv, expected),
           "reverse_KV_error": max_error(reverse_kv, expected),
           "missing_Q_restore_error": max_error(missing_restore, expected)})


@pytest.mark.parametrize("cp", [3, 5])
def test_noncausal_source_prefixes_are_not_global_attention(cp):
    local = 4
    q, k, v = fixture(cp, local)
    q_shards = [[q[i] for i in positions(cp, local, r)] for r in range(cp)]
    ks = [k[r * local:(r + 1) * local] for r in range(cp)]
    vs = [v[r * local:(r + 1) * local] for r in range(cp)]
    actual = source_front_end(q_shards, ks, vs, causal=False)
    full = canonical(q, k, v, causal=False)
    expected_rank0 = [full[i] for i in positions(cp, local, 0)]
    error = max_error(actual[0], expected_rank0)
    assert error > 1e-3  # Counterexample: compiler domain MUST exclude False.
    print({"cp": cp, "noncausal_rank0_error": error,
           "source_rank0": actual[0], "global_rank0": expected_rank0})



def branch_metadata(cp, local, rank):
    """core metadata: Q entries [s,0], K entries [prefix,N-prefix]."""
    half, total = local // 2, cp * local
    return (
        (0, half, half), (0, (rank + 1) * half, total),
        (0, (2 * cp - rank) * half, total),
        tuple(range(half)), tuple(range(half, local)),
    )


def positions(cp, local, rank):
    """varlen_utils.py:115-127, group-local rank (not global device id)."""
    half = local // 2
    return (list(range(rank * half, (rank + 1) * half))
            + list(range((2 * cp - rank - 1) * half,
                         (2 * cp - rank) * half)))


def fixture(cp, local):
    total = cp * local
    # Scaled one-hot position IDs, plus asymmetric shared coordinates.
    q = [[float(i == c) * (1 + i / total) for c in range(total)]
         + [0.2 + i / (2 * total)] for i in range(total)]
    k = [[float(i == c) * (0.7 + i / (3 * total)) for c in range(total)]
         + [0.8 - i / (4 * total)] for i in range(total)]
    v = [[float(i * i + 3 * i + 1), (-1.0) ** i * (i + 0.25)]
         for i in range(total)]
    return q, k, v


def weighted_row(qrow, k, v, allowed):
    """Denote's unshifted exp sum, default 1/sqrt(head_dim), two V channels."""
    logits = [sum(a * b for a, b in zip(qrow, k[j])) / sqrt(len(qrow))
              for j in allowed]
    weights = [exp(logit) for logit in logits]
    return [sum(w * v[j][c] for w, j in zip(weights, allowed)) / sum(weights)
            for c in range(len(v[0]))]


def canonical(q, k, v, causal=True):
    # Independent global mask; no source branch metadata here.
    return [weighted_row(row, k, v, list(range(i + 1 if causal else len(k))))
            for i, row in enumerate(q)]


def source_front_end(q_shards, k_shards, v_shards, causal=True):
    """Two source branches; False is exposed ONLY for the rejection witness."""
    cp, local = len(q_shards), len(q_shards[0])
    k = [row for shard in k_shards for row in shard]
    v = [row for shard in v_shards for row in shard]
    result = []
    for rank, q in enumerate(q_shards):
        cuq, front_cuk, end_cuk, front_idx, end_idx = branch_metadata(cp, local, rank)
        output: list[list[float]] = [[] for _ in range(local)]
        for cuk, idx in ((front_cuk, front_idx), (end_cuk, end_idx)):
            qlen, klen = cuq[1], cuk[1]
            # The second K segment has zero Q rows: no output to compute.
            for a, original_idx in enumerate(idx):
                allowed = [j for j in range(klen)
                           if not causal or j <= a + klen - qlen]
                output[original_idx] = weighted_row(q[original_idx], k, v, allowed)
        result.append(output)
    return result


@pytest.mark.parametrize("cp", [3, 5])
@pytest.mark.parametrize("local", [2, 4, 6])
def test_source_matches_global_at_same_query_positions(cp, local):
    q, k, v = fixture(cp, local)
    q_shards = [[q[i] for i in positions(cp, local, r)] for r in range(cp)]
    k_shards = [k[r * local:(r + 1) * local] for r in range(cp)]
    v_shards = [v[r * local:(r + 1) * local] for r in range(cp)]
    actual = source_front_end(q_shards, k_shards, v_shards)
    full = canonical(q, k, v)
    assert len(actual) == cp
    for rank in range(cp):
        expected = [full[i] for i in positions(cp, local, rank)]
        assert len(actual[rank]) == local
        for got, want in zip(actual[rank], expected):
            assert got == pytest.approx(want, rel=1e-12, abs=1e-12)


@pytest.mark.parametrize("cp,local,rank,front,end", [
    (3, 4, 0, 2, 12), (3, 4, 1, 4, 10), (3, 4, 2, 6, 8),
    (5, 2, 0, 1, 10), (5, 2, 2, 3, 8), (5, 2, 4, 5, 6),
])
def test_exact_source_branch_metadata(cp, local, rank, front, end):
    half, total = local // 2, cp * local
    assert branch_metadata(cp, local, rank) == (
        (0, half, half), (0, front, total), (0, end, total),
        tuple(range(half)), tuple(range(half, local)),
    )
