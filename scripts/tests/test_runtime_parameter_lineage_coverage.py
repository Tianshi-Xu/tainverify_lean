"""Portable multi-parameter raw-port lineage; no captures or value assumptions."""
import copy
from dataclasses import replace
import pytest
from types import SimpleNamespace as NS

from Verdict import graph_to_lean as c
from Verdict.runtime_lineage import Role, consume, trace
from scripts.tests.test_graph_to_lean_runtime_lineage import fixture, IR, T, N


def parameter_fixture(units=2, tp=2):
    sm, pm, authority = fixture(units, tp)
    sm.W.runtime_ndevs = 1
    for world, graph in [('s', sm), ('p', pm)]:
        for rank in range(graph.W.runtime_ndevs):
            width = tp * 3
            k = rank % tp
            weight = IR(40, 'linear.weight', (width, width),
                        ((k*3, (k+1)*3), (0, width)) if world == 'p' else None, True)
            bias = IR(41, 'norm.bias', (width,), param=True)
            # Same shapes do not authenticate activation/gradient parameter roles.
            activation = IR(42, 'unwritten.activation', (width,))
            gradient = IR(43, 'unwritten.gradient', (width,), param=True)
            setattr(gradient, 'is_grad', lambda: True)
            for cid, opname, ins in [(15, 'FW_linear', [weight, activation]),
                                      (16, 'FW_layernorm', [bias, gradient])]:
                refs = [T(world, rank, -1, ir.tid, 0) for ir in ins]
                graph.cells.append(NS(node=N(world, rank, 0, cid, opname), rank=rank,
                    opname=opname, inputs=refs, outputs=[], _input_irs=ins,
                    _output_irs=[], kwargs={}, ir=None))
                graph.shapes.update({ref: ir.shape for ref, ir in zip(refs, ins)})
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), *authority[2:])


def run(sm, pm, authority):
    sv, pv = c._lower_runtime_graphs(sm, pm)
    return sv, pv, trace(sv, pv, *authority)


def test_all_raw_initial_parameters_append_after_existing_four_relations():
    baseline_sm, baseline_pm, baseline_authority = fixture()
    _, _, (baseline, _, _) = run(baseline_sm, baseline_pm, baseline_authority)
    sm, pm, authority = parameter_fixture()
    sv, pv, (lineages, gaps, validation) = run(sm, pm, authority)
    assert len(lineages) == 6
    # Lowered tids depend on the whole tensor inventory; preserve original
    # source endpoints and compare using this view's original _Index mapping.
    from Verdict.runtime_lineage import _Index
    si, pi = _Index(sv, []), _Index(pv, [])
    baseline = tuple(replace(l, target=si.endpoint(l.target.ref), units=tuple(
        replace(u, pieces=tuple(replace(p, endpoint=pi.endpoint(p.endpoint.ref))
                               for p in u.pieces)) for u in l.units)) for l in baseline)
    assert lineages[:4] == baseline
    parameters = [l for l in lineages if l.role == Role.PARAMETER]
    assert [l.target.ref[3] for l in parameters] == [20, 40, 41]
    for lineage in parameters:
        assert lineage.target.phase == 'initial'
        assert lineage.composition == 'unit-parameter-copies'
        assert lineage.obligations == ('initial-parameter-value-equality-unproved',)
        assert [u.unit for u in lineage.units] == [0, 1]
        assert [u.positions for u in lineage.units] == [(), ()]
        assert [[p.endpoint.ref[1] for p in u.pieces] for u in lineage.units] == [[0, 1], [2, 3]]
        assert all(p.endpoint.phase == 'initial' and p.value_part == (0, 1)
                   for u in lineage.units for p in u.pieces)
    assert [u.reconstruction for u in parameters[1].units] == ['tp-axis-gather:0'] * 2
    assert [u.reconstruction for u in parameters[2].units] == ['tp-copy-obligation'] * 2
    result = consume(sv, pv, lineages, gaps, validation, c.backward_closure_tids)
    assert result['coverage']['typed_targets'] == 6
    assert result['proof_admissible'] is False
    assert result['publication'] is False
    assert result['global_complete'] is False


@pytest.mark.parametrize('fault', [
    'missing-rank', 'ambiguous-global-name', 'ambiguous-local-name',
    'mismatched-parent', 'ambiguous-parent-id', 'slices', 'global-slices',
    'value-part', 'coordinated-rank', 'initial-version', 'initial-microbatch',
])
def test_parameter_authority_rejects_missing_ambiguous_or_coordinated_ports(fault):
    sm, pm, authority = parameter_fixture()
    if fault == 'missing-rank':
        pm.cells = [cell for cell in pm.cells if not (cell.rank == 3 and cell.opname == 'FW_linear')]
    elif fault in ('ambiguous-global-name', 'ambiguous-local-name', 'mismatched-parent'):
        graph = sm if fault == 'ambiguous-global-name' else pm
        cell = next(cell for cell in graph.cells if cell.opname == 'FW_layernorm')
        cell._input_irs[0].parent.name = 'linear.weight' if 'ambiguous' in fault else 'other.bias'
    elif fault == 'ambiguous-parent-id':
        cell = copy.deepcopy(next(cell for cell in pm.cells if cell.opname == 'FW_linear'))
        cell.node = cell.node._replace(cid=17)
        cell._input_irs[0].parent.tid += 1
        pm.cells.append(cell)
    else:
        graph = sm if fault == 'global-slices' else pm
        cell = next(cell for cell in graph.cells if cell.opname == 'FW_linear')
        ir = cell._input_irs[0]
        if fault in ('slices', 'global-slices'):
            ir.indmap = ((1, 4), (0, 6))
            graph.shapes[cell.inputs[0]] = (3, 6)
        elif fault == 'value-part': ir.valmap = (1, 2)
        else:
            old = cell.inputs[0]
            new = old._replace(**({'rank': 2} if fault == 'coordinated-rank' else
                {'v': 1} if fault == 'initial-version' else {'mb': 0}))
            cell.inputs[0] = new
            graph.shapes[new] = graph.shapes[old]
    # Exports and retained raw metadata are coordinated, unlike a mere DTO edit.
    authority = (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), *authority[2:])
    with pytest.raises(ValueError): run(sm, pm, authority)


@pytest.mark.parametrize('units,tp', [(2, 2), (3, 3)])
def test_live_value_validator_and_binder_cover_every_parameter_ref(units, tp):
    import torch
    from Verdict.runtime_parameter_inputs import validate
    from Verdict.runtime_initial_relations import bind
    sm, pm, authority = parameter_fixture(units, tp)
    state = {ir.parent.name: torch.arange(ir.parent.shape[0] * (
        ir.parent.shape[1] if len(ir.parent.shape) == 2 else 1), dtype=torch.float32
        ).reshape(ir.parent.shape)
        for cell in sm.cells for ir in cell._input_irs if ir.is_param() and not ir.is_grad()}
    actuals = {}; sources = {}
    for label, graph in [('sm', sm), ('pm', pm)]:
        actuals[label] = []; sources[label] = {}
        for rank in range(graph.W.runtime_ndevs):
            metadata = {}; initialized = {}
            code = ['class GenModel:', f'    rank = {rank}',
                    f'    world_size = {graph.W.runtime_ndevs}', '    def __init__(self):']
            for cell in graph.cells:
                if cell.rank != rank: continue
                for ref, ir in zip(cell.inputs, cell._input_irs):
                    if not ir.is_param() or ir.is_grad(): continue
                    name = f'parameter_{ref.tid}'
                    shape = tuple(ir.parent.shape)
                    slicers = tuple(slice(a, b) for a, b in ir.indmap)
                    code += [f'        self.register_parameter({name!r}, None)',
                        f'        self.add_full_map({name!r}, {ir.parent.tid}, True, '
                        f'{ir.parent.name!r}, {shape!r}, {slicers!r}, 1)']
                    metadata[name] = dict(orig_name=ir.parent.name, shape=list(shape),
                        slicers=[[a, b, None] for a, b in ir.indmap], val_chunks=1)
                    initialized[name] = state[ir.parent.name][slicers].clone()
            sources[label][rank] = '\n'.join(code) + '\n'
            actuals[label].append(dict(metadata=metadata, initialized=initialized))
    sv, pv, (lineages, _, live) = run(sm, pm, authority)
    observations = validate(sv, pv, *authority[:2], actuals, {'state': state}, sources)
    bound = bind(sv, pv, observations, lineages, live)
    assert len(bound['relations']) == 3
    assert sum(len(r['units']) for r in bound['relations']) == 3 * units
    assert len(observations['bindings']) == 3 * (1 + units * tp)
    assert bound['unbound_parameter_refs'] == []
    assert bound['proof_admissible'] is False
    assert bound['kernel_value_proved'] is False
    # A coordinated piece/evidence permutation still has to match a fresh trace.
    target = lineages[-1]
    forged = replace(target, units=tuple(reversed(target.units)))
    observations['bindings'].reverse()
    with pytest.raises(ValueError, match='original raw/batch authority'):
        bind(sv, pv, observations, (*lineages[:-1], forged), live)
