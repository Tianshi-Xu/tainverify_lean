"""Fresh GELU frontier -> direct copied-weight linear candidates, UNCOMPILED.

This is composition only: the existing linear consumer authenticates source,
parameters, schedule and complete output facts. Parent owns assembly and gates.
"""
from Verdict import runtime_frontier_gelu_values as predecessor
from Verdict import runtime_frontier_linear_values as consumer


def render(sm, pm, lineages, validation, bound, execution_order):
    """Refresh GELU once with the SAME six objects; never accept caller receipts."""
    try:
        _, closed = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return consumer._render(sm, pm, lineages, validation, bound, execution_order, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError) as exc:
        raise ValueError(f'malformed frontier-next-linear original source: {exc}') from exc
