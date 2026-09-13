"""Original attention matmul dY (dV) contributions to generic ReduceScatter."""
import pytest

from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from scripts.tests.test_runtime_backward_collective_reads import admitted


def read(admitted, index=132, port=1):
    from Verdict import runtime_backward_collective_reads as collective
    from Verdict import runtime_backward_matmul_reads as matmul
    view, cells, snapshot, order, label = admitted
    return collective.render_read(view, cells, snapshot, index, order, label, matmul.render_read, port)


@pytest.mark.parametrize('index,peers,ranks,local', [
    (132, [131, 367], [0, 1], 0), (368, [131, 367], [0, 1], 1),
    (604, [603, 839], [2, 3], 0), (840, [603, 839], [2, 3], 1)])
def test_original_matmul_dv_reduce_scatter(admitted, index, peers, ranks, local):
    view, cells, snapshot, order, label = admitted
    text, row = read(admitted, index)
    assert row['opname'] == 'ReduceScatterPrim'
    assert row['output_port'] == 1
    assert row['ranks'] == ranks and row['local_index'] == local
    assert [p['source_index'] for p in row['predecessors']] == peers
    assert row['input_refs'] == [list(r) for r in cells[index].inputs]
    assert row['output_ref'] == list(cells[index].outputs[0])
    assert row['execution_index'] == order['source_to_execution'][index]
    assert row['operand_nonwrite_source_indices'] == order['execution_to_source'][row['execution_index']:]
    dim, = row['params']
    shape = list(view.tensor_shape(view.node_inputs(cells[index].node)[0]))
    assert row['input_shapes'] == [shape, shape]
    assert shape[dim] > 0 and shape[dim] % len(ranks) == 0
    shape[dim] //= len(ranks)
    assert row['output_shape'] == shape
    for ref, tid, predecessor in zip(row['input_refs'], row['input_tids'], row['predecessors'], strict=True):
        assert predecessor['output_refs'][1] == ref
        assert predecessor['output_tids'][1] == tid
        assert predecessor['source_contract']['output_roles'] == ['dx', 'dy']
        assert predecessor['theorems'][1].endswith('_dy')
    assert 'SourceReduceScatterRead.reduceScatter_value_of_split' in text
    assert f'chunkPrimDimN {dim} 2 {local} (tensorSum (({row["input_tids"]} : List Tid).map t))' in text
    assert 'bw_matmul' not in text and 'dw' not in text.lower()
    assert text.count('#print axioms') == 1
    assert all(row[k] is False for k in
        ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'))


@pytest.mark.parametrize('fault', [
    'peer-order', 'world-rank', 'inverse', 'execution-reversed', 'dim', 'raw-dim',
    'peer-shape', 'output-shape', 'dy-valmap', 'producer-port0', 'forged-port0',
    'peer-readpoint', 'backward-scale', 'generated-body', 'missing-raw'])
def test_reduce_scatter_rejects_mutations(admitted, monkeypatch, fault):
    import copy
    from dataclasses import replace
    from functools import wraps
    from Verdict import runtime_backward_matmul_reads as matmul
    view, originals, snapshot, order, label = admitted
    clone = copy.copy(view)
    clone.collective_scopes = dict(view.collective_scopes)
    cells, source, execution = list(originals), copy.deepcopy(snapshot), copy.deepcopy(order)
    index, port = 604, 1  # World rank 2 is group-local index 0, not 2.
    node = cells[index].node
    scope = clone.collective_scopes[node]
    writer = next(w for w in source['writers'] if w['export_id'] == scope.source_writer)
    peer = next(w for w in source['writers'] if w['export_id'] == writer['adapter']['peer_writers'][1])
    if fault == 'peer-order':
        clone.collective_scopes[node] = replace(scope, ranks=tuple(reversed(scope.ranks)),
                                               input_tids=tuple(reversed(scope.input_tids)))
    elif fault == 'world-rank':
        clone.collective_scopes[node] = replace(scope, local_index=cells[index].rank)
    elif fault == 'inverse': execution['source_to_execution'][index] += 1
    elif fault == 'execution-reversed': execution['execution_to_source'].reverse()
    elif fault == 'dim': clone.collective_scopes[node] = replace(scope, params=(0,))
    elif fault == 'raw-dim':
        cell = object.__new__(type(cells[index]))
        for slot in cell.__slots__: setattr(cell, slot, getattr(cells[index], slot))
        cells[index] = cell
        cell.kwargs = dict(cell.kwargs, dim=0)
    elif fault in ('peer-shape', 'output-shape'):
        tid = scope.input_tids[1] if fault == 'peer-shape' else scope.output_tid
        original_shape = clone.tensor_shape
        def changed_shape(t):
            shape = list(original_shape(t))
            if t.tid == tid: shape[scope.params[0]] += 1
            return tuple(shape)
        monkeypatch.setattr(clone, 'tensor_shape', changed_shape)
    elif fault == 'dy-valmap':
        # Cell.__getstate__ drops live IR; preserve all transient authority.
        cell = object.__new__(type(cells[839]))
        for slot in cell.__slots__: setattr(cell, slot, getattr(cells[839], slot))
        cells[839] = cell
        cell._output_irs = list(cell._output_irs)
        cell._output_irs[1] = copy.deepcopy(cell._output_irs[1])
        ir = cell._output_irs[1]
        ir._valmap = type(ir._valmap)((0, 1))  # Launder a partial dV into a full value.
    elif fault == 'producer-port0': port = 0
    elif fault == 'forged-port0':
        original = matmul.render_read
        @wraps(original)
        def forged(*args):
            text, row = original(*args)
            row['output_tids'][1] = row['output_tids'][0]
            row['output_refs'][1] = row['output_refs'][0]
            row['theorems'][1] = row['theorems'][0]
            return text, row
        # Both fresh/current invocations return the forged row; actual port
        # authentication, not simply callable identity, must reject it.
        monkeypatch.setattr(matmul, 'render_read', forged)
    elif fault == 'peer-readpoint':
        peer['adapter']['backward_context']['gradient_read_points'][0]['writer'] += '-forged'
    elif fault == 'backward-scale':
        peer['adapter']['backward_context']['runtime']['backward']['kwargs']['scale'] = 0.5
    elif fault == 'generated-body': source.raw_rank_sources['3'] += '\n# forged\n'
    else: source = dict(source)
    with pytest.raises(ValueError):
        read((clone, cells, source, execution, label), index, port)


def test_every_call_reloads_raw_source_and_retains_partial_dv(admitted, monkeypatch):
    import copy
    from Verdict import graph_to_lean as compiler
    view, cells, snapshot, order, label = admitted
    load = compiler._load_chunk_source
    calls = []
    def fresh(*args, **kwargs):
        result = load(*args, **kwargs)
        calls.append(result)
        return result
    monkeypatch.setattr(compiler, '_load_chunk_source', fresh)
    text, row = read(admitted)
    assert len(calls) == 1 and calls[0] is not snapshot
    valmaps = [tuple(cells[p['source_index']]._output_irs[1].valmap) for p in row['predecessors']]
    assert all(v != (0, 1) for v in valmaps)
    assert len(set(valmaps)) == len(row['ranks'])
    for p in row['predecessors']:
        j = p['source_index']
        assert tuple(cells[j]._output_irs[1].valmap) == tuple(calls[0].raw_cells[j]._output_irs[1].valmap)
    corrupted = copy.deepcopy(snapshot)
    corrupted.raw_rank_sources['0'] += '\n# stale authority\n'
    with pytest.raises(ValueError, match='fresh raw writer/generated body'):
        read((view, cells, corrupted, order, label))
    assert len(calls) == 2 and calls[0] is not calls[1]
    assert 'tensorSum' in text


def test_cpu_real_saved_matmul_dv_sum_then_chunk(admitted):
    """Real Torch derivative; independent scalar contraction + collective formula.

    This is CPU formula replay, not a distributed-runtime or Lean refinement claim.
    nnScaler chunks each sender, then torch.distributed.reduce_scatter uses SUM.
    """
    from math import prod
    import torch
    from scripts.tests.test_runtime_backward_matmul_reads import oracle
    _, cells, _, _, _ = admitted
    for index in (132, 604):
        _, row = read(admitted, index)
        dim, = row['params']
        contributions, independent = [], []
        for sender, predecessor in enumerate(row['predecessors']):
            contract = predecessor['source_contract']
            gs, xs, ys = contract['input_shapes']
            x = (torch.arange(prod(xs), dtype=torch.float64) % 11 + 1 + sender * 3).reshape(xs).requires_grad_()
            y = (torch.arange(prod(ys), dtype=torch.float64) % 13 + 2 + sender).reshape(ys).requires_grad_()
            g = (torch.arange(prod(gs), dtype=torch.float64) % 7 + 3 + sender * 5).reshape(gs)
            fw = cells[contract['fw_source_index']]
            assert fw.ir.signature == 'torch.matmul'
            dx, dv = torch.autograd.grad(torch.matmul(x, y), (x, y), g)
            _, expected = oracle(g, x.detach(), y.detach())
            torch.testing.assert_close(dv, expected, rtol=0, atol=0)
            assert dv.unique().numel() > 1 and torch.count_nonzero(dv) == dv.numel()
            if dx.shape == dv.shape: assert not torch.equal(dx, dv)
            contributions.append(dv)
            independent.append(expected)
        assert not torch.equal(*contributions)
        summed = torch.stack(contributions).sum(0)
        shards = summed.chunk(len(row['ranks']), dim=dim)
        for local, rank in enumerate(row['ranks']):
            # Independent path follows runtime order: chunk every sender, SUM
            # the received pieces. Compare against emitted chunk(tensorSum).
            expected = sum((dv.chunk(len(row['ranks']), dim=dim)[local] for dv in independent),
                           torch.zeros_like(shards[local]))
            torch.testing.assert_close(shards[local], expected, rtol=0, atol=0)
            assert list(shards[local].shape) == row['output_shape']
            assert not torch.equal(shards[local], expected / len(row['ranks']))
            assert not torch.equal(shards[local], shards[1-local])
            assert not torch.equal(shards[local], contributions[local].chunk(2, dim=dim)[local])
            if rank >= len(shards):
                with pytest.raises(IndexError): _ = shards[rank]
