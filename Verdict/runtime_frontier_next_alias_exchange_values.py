"""Fresh complete ADD -> original aliases -> hidden/sequence candidates.

Reuse the checked source adapter without re-entering its old residual public
entry point. Every predecessor row and every alias output is passed intact;
unsupported frontiers fail closed in the adapter. Main/skip classification and
SSA-derived declarations are unchanged. Parent owns assembly, cost and kernel
validation; this fragment confers no whole-model or Torch completion claim.
"""
from Verdict import runtime_frontier_add_values as predecessor
from Verdict import runtime_frontier_alias_exchange_values as adapter
from Verdict.runtime_lineage import _same_typed


def render(sm, pm, lineages, validation, bound, execution_order):
    """Fresh SAME-six ADD authority once; no caller-supplied frontier receipt."""
    try:
        _, closed = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, validation, execution_order, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError) as exc:
        raise ValueError(f'malformed next frontier alias/exchange original source: {exc}') from exc


def _render(sm, pm, validation, execution_order, closed):
    # The legacy adapter authenticates original ports/DP/fullrefs. Preserve the
    # newer ADD row's strict typed dimension contract before its older shape
    # comparisons (where Python bool/int equality is insufficient).
    D = len(validation._inputs[3]['config']['units'])
    for row in closed['frontier_units']:
        B, S, H = row['local_shape']
        if (any(type(n) is not int or n <= 0 for n in (B, S, H))
                or not _same_typed(row['dimensions'],
                                   dict(D=D, T=len(row['ranks']), B=B, S=S, H=H))):
            raise ValueError('next frontier complete typed ADD dimensions/local shape mismatch')
    text, result = adapter._render(sm, pm, validation, execution_order, closed)
    # Exchanging an alias with an additional hidden consumer would lose that
    # consumer's input from the returned frontier. Reject the whole candidate,
    # not a filtered branch; the adapter already authenticates these consumers.
    if any(len(row['input_pm_consumers']) != len(row['local_steps'])
           for row in result['exchange_units']):
        raise ValueError('next frontier mixed exchange/hidden fanout unsupported')
    return text, result
