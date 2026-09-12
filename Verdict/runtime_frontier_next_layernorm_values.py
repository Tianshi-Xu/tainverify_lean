"""Fresh complete next alias/exchange -> original LayerNorm candidates.

Reuse the source-authenticating LN adapter, not its earlier public entry point.
Every branch reaches that adapter in original order; retained skips and explicit
unsupported-consumer deferrals keep their complete predecessor facts. No new
math, parameter rebinding, or declaration renaming is needed: names follow SSA.
Parent owns canonical assembly, fixed aggregate cost and kernel validation;
this fragment does not claim whole-model, public or Torch completion.
"""
from Verdict import runtime_frontier_next_alias_exchange_values as predecessor
from Verdict import runtime_frontier_layernorm_values as adapter


def render(sm, pm, lineages, validation, bound, execution_order):
    """Fresh SAME-six predecessor once; no caller-supplied frontier receipt."""
    try:
        _, closed = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return adapter._render(sm, pm, lineages, validation, bound, execution_order, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError) as exc:
        raise ValueError(f'malformed next frontier LayerNorm original source: {exc}') from exc
