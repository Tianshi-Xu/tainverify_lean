"""Authoritative small vectors for YOCO cross-rank semantics.

These tests intentionally use only the Python standard library.  They pin the
position/rank contracts independently of Torch, NCCL, and the current Lean
Denote implementation.
"""

from trainverify.reference.yoco_semantics import (
    causal_sliding_attention_scalar,
    contiguous_rank_chunks,
    distributed_moe,
    local_only_moe,
    select_zigzag_outputs,
    zigzag_cp2_shuffle,
)


def test_cp2_zigzag_shuffle_vector() -> None:
    """YOCO cp=2 changes contiguous shards into outside-in position shards."""
    assert zigzag_cp2_shuffle([[0, 1], [2, 3]]) == [[0, 3], [1, 2]]


def test_cp2_zigzag_output_selection_vector() -> None:
    """Attention output rank ownership follows Q's zigzag positions."""
    full_output = [10, 11, 12, 13]
    assert select_zigzag_outputs(full_output, rank=0, cp_size=2) == [10, 13]
    assert select_zigzag_outputs(full_output, rank=1, cp_size=2) == [11, 12]
    # This is precisely the production-bug counterexample: ordinary chunks
    # have the same shapes, but not the same rank-local values.
    assert contiguous_rank_chunks(full_output, cp_size=2) == [[10, 11], [12, 13]]
    assert select_zigzag_outputs(full_output, 0, 2) != [10, 11]
    assert select_zigzag_outputs(full_output, 1, 2) != [12, 13]


def test_sliding_w1_gather_full_attention_then_contiguous_chunk() -> None:
    """Sliding attention keeps contiguous rank ownership (W <= local chunk)."""
    # Zero q/k makes every allowed key equally weighted.  With causal
    # window=(W, 0), W=1 allows [self] at position 0 and [previous, self]
    # afterwards, giving exact means [0, 1, 3, 5].
    full = causal_sliding_attention_scalar(
        q=[0.0, 0.0, 0.0, 0.0],
        k=[0.0, 0.0, 0.0, 0.0],
        v=[0.0, 2.0, 4.0, 6.0],
        window_left=1,
    )
    assert full == [0.0, 1.0, 3.0, 5.0]
    assert contiguous_rank_chunks(full, cp_size=2) == [[0.0, 1.0], [3.0, 5.0]]


def test_remote_expert_moe_counterexample() -> None:
    """A token routed to a remote expert cannot be evaluated local-only."""
    # Rank 0 owns expert 0 (x -> 2x); rank 1 owns expert 1 (x -> 3x).
    expert_shards = [{0: lambda x: 2 * x}, {1: lambda x: 3 * x}]
    token = 5
    route = 1
    assert distributed_moe(token, route, expert_shards) == 15
    assert local_only_moe(token, route, expert_shards[0]) == 0
    assert distributed_moe(token, route, expert_shards) != local_only_moe(
        token, route, expert_shards[0]
    )
