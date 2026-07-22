"""Dependency-free reference semantics for focused YOCO regression vectors.

This is deliberately not an implementation shim for production code.  It is a
small executable specification used to distinguish operations that happen to
have identical shapes but different rank-local values.
"""

from __future__ import annotations

import math
from collections.abc import Callable, Sequence
from typing import TypeVar

T = TypeVar("T")
Number = int | float
Expert = Callable[[Number], Number]


def zigzag_cp2_shuffle(contiguous_shards: Sequence[Sequence[T]]) -> list[list[T]]:
    """Return outside-in Q shards for the minimal cp=2 authority vector.

    This intentionally locks only the smallest counterexample: two local
    chunks of length two are reconstructed and assigned as positions
    ``[[0, 3], [1, 2]]``.  A future generalized implementation must preserve
    this vector.
    """
    if len(contiguous_shards) != 2 or any(
        len(shard) != 2 for shard in contiguous_shards
    ):
        raise ValueError("the locked cp=2 vector requires two length-two shards")
    full = list(contiguous_shards[0]) + list(contiguous_shards[1])
    return [[full[0], full[3]], [full[1], full[2]]]


def _cp2_positions(sequence_length: int, rank: int) -> list[int]:
    if sequence_length != 4:
        raise ValueError("the locked authority vector has sequence_length=4")
    if rank not in (0, 1):
        raise ValueError("cp=2 rank must be 0 or 1")
    return [[0, 3], [1, 2]][rank]


def select_zigzag_outputs(
    full_output: Sequence[T], rank: int, cp_size: int = 2
) -> list[T]:
    """Select output positions owned by rank-local zigzag Q for the cp=2 vector."""
    if cp_size != 2:
        raise ValueError("this regression reference is specifically for cp_size=2")
    return [full_output[i] for i in _cp2_positions(len(full_output), rank)]


def contiguous_rank_chunks(values: Sequence[T], cp_size: int) -> list[list[T]]:
    """Split a full sequence into ordinary contiguous equal rank chunks."""
    if cp_size <= 0 or len(values) % cp_size:
        raise ValueError("sequence length must be divisible by positive cp_size")
    width = len(values) // cp_size
    return [list(values[r * width : (r + 1) * width]) for r in range(cp_size)]


def causal_sliding_attention_scalar(
    q: Sequence[float],
    k: Sequence[float],
    v: Sequence[float],
    window_left: int,
) -> list[float]:
    """Naive scalar softmax attention with YOCO's causal window ``(W, 0)``."""
    if not (len(q) == len(k) == len(v)):
        raise ValueError("q, k, and v lengths must match")
    if window_left < 0:
        raise ValueError("window_left must be nonnegative")
    outputs: list[float] = []
    for query_pos, query in enumerate(q):
        first_key = max(0, query_pos - window_left)
        positions = range(first_key, query_pos + 1)
        scores = [query * k[key_pos] for key_pos in positions]
        normalizer_shift = max(scores)
        weights = [math.exp(score - normalizer_shift) for score in scores]
        normalizer = sum(weights)
        outputs.append(
            sum(weight * v[key_pos] for weight, key_pos in zip(weights, positions))
            / normalizer
        )
    return outputs


def distributed_moe(
    token: Number, route: int, expert_shards: Sequence[dict[int, Expert]]
) -> Number:
    """Evaluate the routed expert wherever it is owned across all rank shards."""
    owners = [experts[route] for experts in expert_shards if route in experts]
    if len(owners) != 1:
        raise ValueError("the route must have exactly one expert owner")
    return owners[0](token)


def local_only_moe(token: Number, route: int, local_experts: dict[int, Expert]) -> Number:
    """Model one shard's masked contribution; a remote route contributes zero."""
    expert = local_experts.get(route)
    return 0 if expert is None else expert(token)
