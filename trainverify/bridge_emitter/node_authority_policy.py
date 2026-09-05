"""Canonical graph-node identity projection for relation authority."""
from __future__ import annotations

from typing import Protocol


class NodeAuthorityView(Protocol):
    rank: int
    op: str
    ins: list[int]
    outs: list[int]
    params: list[int] | None


def node_authority_fingerprint(
    node: NodeAuthorityView,
) -> tuple[int, str, tuple[int, ...], tuple[int, ...], tuple[int, ...]]:
    """Return the canonical node identity shared by coverage and schedule digests."""
    return (
        int(node.rank),
        str(node.op),
        tuple(int(value) for value in node.ins),
        tuple(int(value) for value in node.outs),
        tuple(int(value) for value in (node.params or ())),
    )
