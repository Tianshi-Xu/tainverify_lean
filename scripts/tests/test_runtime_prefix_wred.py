"""Computed WRED prefixes preserve source-scoped versioned SUM writers."""
import re
import pytest
from copy import deepcopy
from types import SimpleNamespace as NS

from Verdict import graph_to_lean as c
from Verdict.runtime_world import render
from Verdict.runtime_input_feed import bind
from scripts.tests.test_graph_to_lean_wred_scope import fixture as reducer_fixture, tref
from scripts.tests.test_graph_to_lean_runtime_lineage import Graph, T, N, IR
from scripts.tests.test_runtime_input_feed import observed
from scripts.tests.test_runtime_scoped_prefix import proof_text
from trainverify.runtime_source_authority import build_snapshot, bind_reducers


def wred_world(root, ranks=(0, 2), *, fault=None):
    """Real scope authentication and CPU feeds; synthetic source-model producers.

    Parameter ownership is a fixture input, not a claim that the forward
    embedding values here are derivatives. Actual backward coverage is tested
    separately against the captured model's versioned reducer authority.
    """
    g, snapshot, raw, sources = reducer_fixture(ranks, shape=(2, 2))
    world = g.W.runtime_ndevs
    feed_authority = observed(root, 1, world)
    sm, pm = Graph('s', 1, world), Graph('p', 1, world)
    pm.cells = []; pm.shapes = {}
    rows = []
    for rank in range(world):
        loader = next(x for x in Graph('p', 1, world).cells
                      if x.rank == rank and x.opname == 'DATALOADER')
        pm.cells.append(loader)
        pm.shapes.update({t: ir.shape for t, ir in zip(loader.outputs, loader._output_irs)})
        row = dict(ref=dict(world='p', runtime_rank=rank, microbatch=0,
                            source_cid=5, call_instance=0, op='DATALOADER', origin='nnscaler'),
                   source_irname='DATALOADER', inputs=[], outputs=[tref(t) for t in loader.outputs],
                   parameter_grad_tids=[])
        rows.append(row); raw[loader.node] = dict(ref=deepcopy(row['ref']), parameter_grad_tids=[])
        if rank not in ranks:
            continue
        x = T('p', rank, 0, 12, 1)
        view = NS(node=N('p', rank, 0, 6, 'FW_view'), rank=rank, opname='FW_view',
                  kwargs={'size': (2,)}, inputs=[loader.outputs[1]], outputs=[x],
                  _input_irs=[IR(11, 'ids', (1, 2))], _output_irs=[IR(12, 'ids', (2,))])
        pm.cells.append(view); pm.shapes[x] = (2,)
        row = dict(ref=dict(world='p', runtime_rank=rank, microbatch=0, source_cid=6,
                            call_instance=0, op='FW_view', origin='nnscaler'), source_irname='FW_view',
                   inputs=[tref(t) for t in view.inputs], outputs=[tref(x)], parameter_grad_tids=[])
        rows.append(row); raw[view.node] = dict(ref=deepcopy(row['ref']), parameter_grad_tids=[])
        for old in (n for n in g.nodes() if n.rank == rank):
            op = str(g.node_opname(old)).split('.')[-1]
            inputs = [T(*t) for t in g.node_inputs(old)]
            outputs = [T(*t) for t in g.node_outputs(old)]
            if op == 'FW_embedding': inputs = [x, *inputs]
            cell = NS(node=N(*old), rank=rank, opname=op,
                      kwargs={'start': 0, 'stop': 2, 'padding_idx': None} if op == 'FW_embedding' else {},
                      inputs=inputs, outputs=outputs,
                      _input_irs=[IR(t.tid, 'weight' if t.v == 0 else 'value',
                                     (2,) if t == x else (2, 2), param=t.v == 0) for t in inputs],
                      _output_irs=[IR(t.tid, 'value', (2, 2)) for t in outputs])
            cell.ir = NS(mirror=NS(cid=old.cid+100),
                         inputs=lambda cell=cell: cell._input_irs,
                         outputs=lambda cell=cell: cell._output_irs)
            pm.cells.append(cell)
            pm.shapes.update({t: (2, 2) for t in [*inputs, *outputs] if t != x})
            row = deepcopy(next(w for w in snapshot['writers'] if w['ref'] == raw[old]['ref']))
            row['inputs'] = [tref(t) for t in inputs]; rows.append(row)
    combined = build_snapshot(rows)
    combined.update(runtime_ndevs=world, rank_sources=sources)
    for t in combined['tensors']:
        match = next((x for x in snapshot['tensors'] if x['ref'] == t['ref']), {})
        if 'placement' in match: t['placement'] = deepcopy(match['placement'])
    bind_reducers(combined)
    sv, pv = c._lower_runtime_graphs(sm, pm)
    c.attach_wred_scopes(pv, combined, raw, sources)
    if fault == 'stale-scope':
        from dataclasses import replace
        node = next(iter(pv.wred_scopes))
        pv.wred_scopes[node] = replace(pv.wred_scopes[node], input_tids=tuple(reversed(pv.wred_scopes[node].input_tids)))
    legacy = render(sv, pv, sm.cells, pm.cells)
    return bind(legacy, sv, pv, sm.cells, pm.cells, *feed_authority, root)


@pytest.mark.parametrize('ranks', [(2,), (0, 2), (1, 3, 5)])
def test_computed_wred_only_boundary_has_full_prefix(tmp_path, ranks):
    fed = wred_world(tmp_path, ranks)
    p = fed.receipt['scoped_prefix']['pm']
    assert p['frontier'] is None
    assert p['prefix_nodes'] == fed.receipt['execution_order']['pm']['execution_to_source']
    text = proof_text(fed)
    assert ':= cross_dp_wred [' in text
    assert 'WredContract' in text
    for suffix in ('Success', 'Output', 'OutputShape', 'Frame', 'Continuation'):
        assert 'pmPrefix' + suffix in p['kernel_checks']
    assert fed.receipt['proof_admissible'] is False
    assert fed.receipt['public_complete'] is False
    nodes = re.findall(r'def pmNode_(\d+) : NodeDecl := \{rank := (\d+), op := "OpName.CROSS_DP_WRED", ins := \[([^]]+)\], outs := \[(\d+)\]', text)
    assert tuple(int(rank) for _, rank, _, _ in nodes) == ranks
    assert len(p['guards']) == len(ranks)
    values = []
    for index, rank, inputs, output in nodes:
        tids = [int(t) for t in inputs.split(',')]
        assert int(output) not in tids
        j = p['prefix_nodes'].index(int(index))
        guard = next(g for g in p['guards'] if g['execution_index'] == j)
        assert guard['input_tids'] == tids
        assert guard['output_tid'] == int(output)
        assert guard['operand_shapes'] == [[2, 2]] * len(ranks)
        assert f'WredContract {list(ranks)} (pmPeers pmNode_{index}) (pmPrefixState_{j} init) pmNode_{index}' in text
        value = re.search(rf'def pmPrefixValue_{j}_0 .* := ([^\n]+)', text)[1]
        values.append(value)
        assert f'(pmPrefixState_{j+1} init) {output} = pmPrefixValue_{j}_0 init' in text
        assert f'(h : tid ∉ [{output}]) : (pmPrefixState_{j+1} init) tid = (pmPrefixState_{j} init) tid' in text
    # Later versioned writers must still read the same old contribution values.
    assert len(set(values)) == 1
    assert values[0].startswith('cross_dp_wred [')
    assert len(p['initial_premises']) == len(ranks)


def test_wred_prefix_rejects_stale_scope_before_render(tmp_path):
    with pytest.raises(ValueError, match='stale attached scope'):
        wred_world(tmp_path, fault='stale-scope')
