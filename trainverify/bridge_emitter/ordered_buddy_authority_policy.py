"""Pure ordered context-parallel buddy authority validation."""
from __future__ import annotations

from dataclasses import dataclass
from enum import Enum


@dataclass(frozen=True)
class OrderedBuddyRow:
    node_key: int
    op: str
    parameters: tuple[int, ...]
    input_tids: tuple[object, ...]


class OrderedBuddyFailure(str, Enum):
    INVALID_CP_SIZE = "invalid-cp-size"
    INCOMPLETE = "incomplete"
    OUT_OF_ORDER = "out-of-order"
    OP_MISMATCH = "op-mismatch"
    PARAMETER_MISMATCH = "parameter-mismatch"
    SIGNATURE_MISMATCH = "signature-mismatch"
    UNIFORM_SIGNATURE_MISMATCH = "uniform-signature-mismatch"
    METADATA_MISMATCH = "metadata-mismatch"
    CURRENT_NODE_MISMATCH = "current-node-mismatch"


@dataclass(frozen=True)
class OrderedBuddyDecision:
    metadata_tid: int | None = None
    failure: OrderedBuddyFailure | None = None


def check_ordered_cp_buddy_authority(
    rows: tuple[OrderedBuddyRow, ...],
    *,
    cp_size: int,
    expected_op: str,
    current_node_key: int | None = None,
) -> OrderedBuddyDecision:
    """Validate ordered PM buddy rows without importing graph/compiler types."""
    if cp_size <= 1:
        return OrderedBuddyDecision(failure=OrderedBuddyFailure.INVALID_CP_SIZE)
    if len(rows) != cp_size:
        return OrderedBuddyDecision(failure=OrderedBuddyFailure.INCOMPLETE)
    if any(row.op != expected_op for row in rows):
        return OrderedBuddyDecision(failure=OrderedBuddyFailure.OP_MISMATCH)
    if any(
        len(row.parameters) != 2 or row.parameters[0] != cp_size for row in rows
    ):
        return OrderedBuddyDecision(failure=OrderedBuddyFailure.PARAMETER_MISMATCH)
    if tuple(row.parameters[1] for row in rows) != tuple(range(cp_size)):
        return OrderedBuddyDecision(failure=OrderedBuddyFailure.OUT_OF_ORDER)
    input_arities = tuple(len(row.input_tids) for row in rows)
    if any(arity != 2 for arity in input_arities):
        failure = (
            OrderedBuddyFailure.UNIFORM_SIGNATURE_MISMATCH
            if all(arity != 2 for arity in input_arities)
            else OrderedBuddyFailure.SIGNATURE_MISMATCH
        )
        return OrderedBuddyDecision(failure=failure)
    metadata_tids = tuple(row.input_tids[1] for row in rows)
    if len(set(metadata_tids)) != 1:
        return OrderedBuddyDecision(failure=OrderedBuddyFailure.METADATA_MISMATCH)
    if current_node_key is not None:
        matches = tuple(row for row in rows if row.node_key == current_node_key)
        if len(matches) != 1:
            return OrderedBuddyDecision(failure=OrderedBuddyFailure.CURRENT_NODE_MISMATCH)
        local_rank = matches[0].parameters[1]
        if rows[local_rank].node_key != current_node_key:
            return OrderedBuddyDecision(failure=OrderedBuddyFailure.CURRENT_NODE_MISMATCH)
    return OrderedBuddyDecision(metadata_tid=metadata_tids[0])
