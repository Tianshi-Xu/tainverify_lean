"""Portable census fixtures: live raw ports and real source-scope authentication."""
import copy
import importlib.util
from dataclasses import replace
from types import SimpleNamespace as NS

import pytest
from Verdict import graph_to_lean as c
from Verdict.runtime_lineage import trace
from scripts.tests.test_graph_to_lean_runtime_lineage import fixture, IR, T, N


def discover(sm, pm, authority):
    sv, pv = c._lower_runtime_graphs(sm, pm)
    if any(x.opname == 'ChunkPrim' for x in pm.cells):
        c.attach_collective_scopes(pv, authority[2])
    ls, _, validation = trace(sv, pv, *authority)
    assert importlib.util.find_spec('Verdict.runtime_embedding_routes'), 'missing embedding route census'
    from Verdict.runtime_embedding_routes import census
    return sv, pv, ls, validation, census


def adapter_fixture(units=2, tp=2, seqlen=2):
    from trainverify.runtime_source_authority import build_snapshot, bind_adapters, bind_reducers
    from scripts.tests.test_graph_to_lean_collective_scope import tref
    sm, pm, old = fixture(units, tp, seqlen)
    sm.W.runtime_ndevs = 1
    width = tp * 3
    for world, graph in [('s', sm), ('p', pm)]:
        for rank in range(graph.W.runtime_ndevs):
            b = units if world == 's' else 1
            k = rank % tp
            loader = next(x for x in graph.cells if x.rank == rank and x.opname == 'DATALOADER')
            pos = loader._output_irs[1]
            weight = IR(40, 'position.weight', (32, width), param=True)
            sliced = IR(51, 'position_ids', (b, seqlen), ((0, b), (k*(seqlen//tp), (k+1)*(seqlen//tp))))
            y = IR(50, 'position.embedding', (b, seqlen, width),
                   (*sliced.indmap, (0, width)) if world == 'p' else None)
            out = IR(52, 'position.embedding', (b, seqlen, width), ((0, b), (0, seqlen), (k*3, (k+1)*3)))
            refs = lambda ir: T(world, rank, -1 if ir.param else 0, ir.tid, 0 if ir.param else 1)
            def add(cid, operation, inputs, outputs, kw, kind=None, inrefs=None):
                cell = NS(node=N(world, rank, 0, cid, kind or operation), rank=rank,
                    opname=operation, inputs=inrefs or [refs(ir) for ir in inputs],
                    outputs=[refs(ir) for ir in outputs], _input_irs=inputs,
                    _output_irs=outputs, kwargs=kw)
                cell.ir = NS(signature=operation, mirror=NS(cid=cid+100),
                             inputs=lambda cell=cell: cell._input_irs,
                             outputs=lambda cell=cell: cell._output_irs)
                graph.cells.append(cell)
                graph.shapes.update({refs(ir): ir.shape for ir in [*inputs, *outputs]})
            ranks = list(range(rank//tp*tp, (rank//tp+1)*tp))
            if world == 'p':
                add(12, 'ChunkPrim', [pos], [sliced], dict(ranks=ranks, dim=1))
            add(13, 'FW_embedding', [sliced if world == 'p' else pos, weight], [y],
                dict(start=0, stop=32, padding_idx=None))
            if world == 'p':
                add(14, 'AllToAllPrim', [y], [out], dict(ranks=ranks, idim=1, odim=2),
                    inrefs=[T('p', r, 0, y.tid, 1) for r in ranks])
    writers, prepared = [], []
    for cell in pm.cells:
        row = dict(ref=dict(world='p', runtime_rank=cell.rank, microbatch=0,
                   source_cid=cell.node.cid, call_instance=0, op=cell.opname, origin='fixture'),
                   source_irname=cell.node.irname, inputs=[tref(t) for t in cell.inputs],
                   outputs=[tref(t) for t in cell.outputs], parameter_grad_tids=[])
        adapter = copy.deepcopy(row)
        if cell.opname in ('ChunkPrim', 'AllToAllPrim'):
            row['adapter_kwargs'] = copy.deepcopy(cell.kwargs)
            adapter['primitive'] = dict(kind=cell.node.irname, forward=True, kwargs=copy.deepcopy(cell.kwargs))
            adapter['inputs'] = [tref(t) for t in cell.inputs if t.rank == cell.rank]
            prim = adapter['primitive']
            prim.update(signature='nnscaler.runtime.adapter.' + ('chunk' if cell.opname == 'ChunkPrim' else 'all_to_all'),
                        generated_inputs=['position_ids_11' if cell.opname == 'ChunkPrim' else 'position_emb_50'],
                        generated_outputs=['position_ids_51' if cell.opname == 'ChunkPrim' else 'position_emb_52'])
            if cell.opname == 'ChunkPrim':
                from scripts.tests.test_graph_to_lean_chunk_scope import fixture as chunk_fixture
                prim['runtime'] = chunk_fixture()[1]['adapter_source'][1]['primitive']['runtime']
        if cell.opname == 'DATALOADER':
            adapter = copy.deepcopy(next(r for r in old[2]['adapter_source']
                if r['ref']['op'] == 'DATALOADER' and r['ref']['runtime_rank'] == cell.rank))
        writers.append(row); prepared.append(adapter)
    snapshot = build_snapshot(writers)
    snapshot.update(source=copy.deepcopy(old[2]['source']), runtime_ndevs=units*tp,
                    rank_sources=copy.deepcopy(old[2]['rank_sources']), adapter_source=prepared)
    for rank in range(units*tp):
        ranks = list(range(rank//tp*tp, (rank//tp+1)*tp))
        snapshot['rank_sources'][str(rank)] = snapshot['rank_sources'][str(rank)].replace(
            'def segment9(self, input_ids_10, position_ids_11): pass',
            'def segment9(self, input_ids_10, position_ids_11):\n'
            f'        position_ids_51 = nnscaler.runtime.adapter.chunk(position_ids_11, dim=1, ranks={ranks})\n'
            '        position_emb_50 = embedding(position_ids_51, self.weight_40)\n'
            f'        position_emb_52 = nnscaler.runtime.adapter.all_to_all(position_emb_50, idim=1, odim=2, ranks={ranks})')
    bind_reducers(snapshot)
    bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *old[3:])


@pytest.mark.parametrize('units,tp', [(2, 2), (3, 2), (2, 1)])
def test_chunk_embedding_exchange_routes(units, tp):
    sm, pm, authority = adapter_fixture(units, tp)
    sv, pv, ls, validation, census = discover(sm, pm, authority)
    result = census(sv, pv, ls, validation)
    assert not result.unavailable
    assert len(result.routes) == units * 2
    assert len(ls) == 5  # no synthetic activation relation for the second embedding
    for route in result.routes[units:]:
        assert route.batch_key == ls[1].target.ref
        assert route.parameter_key == ls[-1].target.ref
        assert route.global_embedding.inputs[0].endpoint == ls[1].target
        for rank in route.ranks:
            assert rank.chunk.chunk_axis == rank.exchange.gather_axis == 1
            assert rank.exchange.split_axis == 2
            assert rank.chunk.inputs == (rank.loader,)
            assert rank.chunk.outputs == (rank.embedding.inputs[0],)
            assert rank.output.endpoint.ref[3] == 52
            assert rank.output.bounds == ((0, 1), (0, 2), (rank.exchange.local_index*3, (rank.exchange.local_index+1)*3))
            assert tuple(p.endpoint.tid for p in rank.exchange.inputs) == tuple(tid for _, tid in rank.exchange.peers)
            assert rank.exchange.ranks == tuple(r.rank for r in route.ranks)
            assert rank.exchange.inputs[rank.exchange.local_index] == rank.embedding.outputs[0]


@pytest.mark.parametrize('fault', ['plain-validation', 'lineage-order', 'positions', 'raw-port', 'scope', 'peer-order', 'bool-ref', 'bool-layout', 'bool-scope'])
def test_malformed_identity_is_not_unavailable(fault):
    sm, pm, authority = adapter_fixture()
    sv, pv, ls, validation, census = discover(sm, pm, authority)
    if fault == 'plain-validation': validation = dict(validation)
    elif fault == 'lineage-order': ls = tuple(reversed(ls))
    elif fault == 'positions':
        ls = (replace(ls[0], units=(replace(ls[0].units[0], positions=(1,)), *ls[0].units[1:])), *ls[1:])
    elif fault == 'raw-port':
        next(x for x in authority[1] if x.node.cid == 13).inputs.reverse()
    elif fault == 'scope':
        node = next(iter(pv.collective_scopes))
        pv.collective_scopes[node] = replace(pv.collective_scopes[node], params=(2, 1))
    elif fault == 'bool-layout':
        ir = next(x for x in authority[1] if x.node.cid == 13)._output_irs[0]
        ir.indmap = ((False, 1), *ir.indmap[1:])
    elif fault == 'bool-scope':
        node = next(iter(pv.collective_scopes))
        pv.collective_scopes[node] = replace(pv.collective_scopes[node], local_index=False)
    elif fault == 'peer-order':
        node = next(iter(pv.collective_scopes))
        pv._node2inputs[node].reverse()
    else:
        t = sv.tensors()[0]
        original = sv._original[t.tid]
        sv._original[t.tid] = original._replace(rank=False)
    with pytest.raises(ValueError): census(sv, pv, ls, validation)


@pytest.mark.parametrize('world', ['s', 'p'])
@pytest.mark.parametrize('fault', ['input-rank', 'input-version', 'node-mb', 'owner'])
def test_independent_raw_boolean_identity_rejects_before_retrace(world, fault):
    sm, pm, authority = fixture()
    sm.W.runtime_ndevs = 1
    sv, pv, ls, validation, census = discover(sm, pm, authority)
    raw = authority[0 if world == 's' else 1]
    cell = next(x for x in raw if x.opname == 'FW_embedding' and x.rank == 0)
    if fault == 'input-rank':
        cell.inputs[0] = cell.inputs[0]._replace(rank=False)
    elif fault == 'input-version':
        cell.inputs[0] = cell.inputs[0]._replace(v=True)
    elif fault == 'node-mb':
        cell.node = cell.node._replace(mb=False)
    else:
        cell.rank = False
    with pytest.raises(ValueError, match='raw.*identity'):
        census(sv, pv, ls, validation)


@pytest.mark.parametrize('fault', ['node-world', 'node-owner', 'output-owner', 'output-version'])
def test_raw_node_and_output_ownership_rejects_before_retrace(fault):
    sm, pm, authority = fixture()
    sm.W.runtime_ndevs = 1
    sv, pv, ls, validation, census = discover(sm, pm, authority)
    cell = next(x for x in authority[1] if x.opname == 'FW_embedding' and x.rank == 0)
    if fault == 'node-world': cell.node = cell.node._replace(wtype='s')
    elif fault == 'node-owner': cell.rank = 1
    elif fault == 'output-owner': cell.outputs[0] = cell.outputs[0]._replace(rank=1)
    else: cell.outputs[0] = cell.outputs[0]._replace(v=True)
    with pytest.raises(ValueError, match='raw.*identity'):
        census(sv, pv, ls, validation)


def test_unknown_input_adapter_is_explicit_unavailable():
    sm, pm, authority = adapter_fixture()
    # A valid source graph using a different local operator, not a forged scope.
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers
    for cell in pm.cells:
        if cell.opname == 'ChunkPrim':
            cell.opname = 'FW_contiguous'
            cell.node = cell.node._replace(irname='FW_contiguous')
            cell.kwargs = {}
    # No source scoped operations are left; the ordinary chain is unsupported.
    pm.cells = [x for x in pm.cells if x.opname != 'AllToAllPrim']
    snapshot = copy.deepcopy(authority[2])
    writers = [w for w in snapshot['writers'] if w['ref']['op'] != 'AllToAllPrim']
    for w in writers:
        if w['ref']['op'] == 'ChunkPrim':
            w['ref']['op'] = 'FW_contiguous'
            w['source_irname'] = 'FW_contiguous'
            w.pop('chunk_scope', None)
            w.pop('adapter_kwargs', None)
    fresh = build_snapshot(writers)
    fresh.update({k: snapshot[k] for k in ('source', 'runtime_ndevs', 'rank_sources')})
    fresh['adapter_source'] = [a for a in snapshot['adapter_source'] if a['ref']['op'] != 'AllToAllPrim']
    for a in fresh['adapter_source']:
        if a['ref']['op'] == 'ChunkPrim':
            a['ref']['op'] = 'FW_contiguous'
            a['source_irname'] = 'FW_contiguous'
            a.pop('primitive')
            a.pop('adapter_kwargs', None)
    for rank, text in fresh['rank_sources'].items():
        text = text.replace('nnscaler.runtime.adapter.chunk', 'unknown_adapter')
        fresh['rank_sources'][rank] = '\n'.join(line for line in text.splitlines() if 'adapter.all_to_all' not in line) + '\n'
    bind_reducers(fresh)
    from trainverify.runtime_source_authority import bind_adapters
    bind_adapters(fresh)
    snapshot = fresh
    sv, pv = c._lower_runtime_graphs(sm, pm)
    raw = (authority[0], copy.deepcopy(pm.cells), snapshot, *authority[3:])
    ls, _, validation = trace(sv, pv, *raw)
    from Verdict.runtime_embedding_routes import census
    result = census(sv, pv, ls, validation)
    assert len(result.routes) == 2
    assert len(result.unavailable) == 2
    assert all('unsupported loader-to-embedding path' == x.reason for x in result.unavailable)


def test_direct_routes_keep_original_order_and_lineage_keys():
    sm, pm, authority = fixture(3, 3)
    sm.W.runtime_ndevs = 1
    sv, pv, ls, validation, census = discover(sm, pm, authority)
    before = copy.deepcopy(ls)
    result = census(sv, pv, ls, validation)
    assert ls == before
    assert [r.unit for r in result.routes] == [0, 1, 2]
    assert not result.unavailable
    for route in result.routes:
        assert route.batch_key == ls[0].target.ref
        assert route.parameter_key == ls[2].target.ref
        assert route.global_embedding.inputs[0].endpoint == ls[0].target
        assert route.global_embedding.outputs[0].endpoint == ls[3].target
        assert [r.rank for r in route.ranks] == list(range(route.unit * 3, (route.unit + 1) * 3))
        for rank in route.ranks:
            assert rank.chunk is None and rank.exchange is None
            assert rank.embedding.inputs[0].endpoint == rank.loader.endpoint
            assert rank.output == rank.embedding.outputs[0]
    assert result.proof_admissible is result.public_complete is False
    assert result.kernel_value_proved is result.torch_refinement is False
