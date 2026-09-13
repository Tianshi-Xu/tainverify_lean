"""Selective forward projection-input AA(1,2) candidates, UNCOMPILED.

Fresh sequence-alias facts are the only predecessor authority. PM K/V exchange
advances saved prerequisites for backward; SM linear and Q's sequence AllGather
are not consumed. This is not full forward, kernel, or Torch acceptance.
"""
from dataclasses import asdict

from Verdict import runtime_frontier_sequence_alias_values as predecessor
from Verdict import runtime_frontier_sequence_hidden_values as selective
from Verdict.runtime_lineage import _Index, _same_typed, op


def _aliases(sm, pm, validation, closed):
    """Bind complete alias descriptors and every source slot, even deferred Q."""
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    groups = {}
    for row in closed['frontier_units']:
        if 'slot' in row and not _same_typed(row['slot'], row['source_output_slot']):
            raise ValueError('projection exchange original alias slot mismatch')
        descriptors = [(si, row['source_step']), *((pi, s) for s in row['local_steps'])]
        for index, descriptor in descriptors:
            cell = index.raw[tuple(descriptor['node'])]
            if op(cell) == 'FW_multiref':
                predecessor.alias.residual._identity(index, cell)
                inputs = predecessor.alias._ports(index, cell, 'inputs')
                predecessor.alias._ports(index, cell, 'outputs')
                if len(inputs) != 1:
                    raise ValueError('projection exchange original alias input arity mismatch')
                predecessor.alias._edge(index, inputs[0], cell._input_irs[0])
                step = predecessor.post._next(index, inputs[0])
                if not _same_typed(asdict(step), descriptor):
                    raise ValueError('projection exchange complete original alias descriptor mismatch')
        g = predecessor.layernorm._output(si, row['source_step'], row['sm_output_ref'])
        ps = [predecessor.layernorm._output(pi, step, ref) for step, ref in
              zip(row['local_steps'], row['pm_output_refs'], strict=True)]
        parent = predecessor.alias._original(si, g).parent.tid
        if any(not _same_typed(predecessor.alias._original(pi, p).parent.tid, parent) for p in ps):
            raise ValueError('projection exchange original SM/PM peer parent identity mismatch')
        if row['gather_axis'] == 1 and row['source_step']['op'] == 'FW_multiref':
            key = (tuple(row['source_step']['node']), row['unit'])
            slots, count = groups.setdefault(key, ([], len(row['source_step']['outputs'])))
            slots.append(row['source_output_slot'])
    if any(not _same_typed(slots, list(range(count))) for slots, count in groups.values()):
        raise ValueError('projection exchange complete ordered original alias slots required')


def render(sm, pm, lineages, validation, bound, execution_order):
    """Reconstruct the predecessor exactly once from the SAME six objects."""
    try:
        _, closed = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, lineages, validation, bound, execution_order, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError) as exc:
        raise ValueError(f'malformed frontier projection exchange original source: {exc}') from exc


def _render(sm, pm, lineages, validation, bound, order, closed):
    _aliases(sm, pm, validation, closed)
    text, result = selective._render(sm, pm, validation, order, closed,
        consumer_fn=predecessor._consumers, sm_consumer_ops=((), ('FW_add',), ('FW_linear',)),
        theorem_stem='frontierProjectionExchange')
    for row in result['deferred_units']:
        if any('AllGatherPrim' in kinds for kinds in row['observed_consumer_ops'][1:]):
            row['reason'] = 'sequence AllGather(dim=1) deferred; projection and Q values not consumed'
    result.update(status='source-frontier-projection-exchange-values-emitted-uncompiled',
        cost_scope='selective projection-input exchange fragment only; excludes predecessors, frame and imports')
    return text, result
