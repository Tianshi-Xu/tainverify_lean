"""Actual captured BW_linear source boundary; no recapture or rank-cell cache.

Run with TRAINVERIFY_CAPTURE_ROOT pointing at the existing global-b2/p2-r4
capture directory. These are trusted local pickle inputs, not upload readers.
"""
import copy
import importlib
import importlib.util
import json
import os
import pickle
from pathlib import Path

import pytest


@pytest.fixture(scope='module')
def captured():
    root = os.environ.get('TRAINVERIFY_CAPTURE_ROOT')
    if not root:
        pytest.skip('set TRAINVERIFY_CAPTURE_ROOT to trusted existing captures')
    from nnscaler_backend.build_graph import _prepare_rank_cells
    from verdict.graph import World, WType
    cases = []
    for name, label in [('global-b2', 's'), ('p2-r4', 'p')]:
        path = Path(root) / name / 'capture.pkl'
        with path.open('rb') as stream:
            mg = pickle.load(stream)
        world = World(wtype=WType(label), plan_ndevs=len(mg.devices), runtime_ndevs=mg.runtime_ndevs,
                      **json.loads(path.with_suffix('.json').read_text()))
        for rank in range(world.runtime_ndevs):
            cells = _prepare_rank_cells(world, mg, rank)
            index = next(i for i, c in enumerate(cells) if c.opname.name == 'BW_linear')
            cases.append((cells, index))
    return cases


def api():
    assert importlib.util.find_spec('trainverify.backward_linear_authority') is not None, \
        'BW_linear has no original mirror/saved-version authority boundary'
    return importlib.import_module('trainverify.backward_linear_authority').bind


def test_actual_first_bw_linear_binds_saved_primal_and_gradient_roles(captured):
    bind = api()
    for cells, index in captured:
        cell = cells[index]
        contract = bind(cells, index)
        forward = next(c for c in cells if c.ir is cell.ir.mirror)
        assert contract['bw_node'] == list(cell.node)
        assert contract['fw_node'] == list(forward.node)
        assert contract['inputs'] == [list(r) for r in cell.inputs]
        assert contract['outputs'] == [list(r) for r in cell.outputs]
        assert contract['saved_inputs'] == [list(r) for r in forward.inputs]
        assert contract['input_roles'] == ['cotangent', 'saved_input', 'saved_weight']
        assert contract['output_roles'] == ['dx', 'dw']
        assert contract['weight_layout'] == 'out_features,in_features'
        assert contract['reduction_axes'] == list(range(len(cell._input_irs[1].shape)-1))
        assert contract['scale'] == 'supplied-cotangent; no additional local scaling'
        assert all(contract[k] is False for k in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'))


@pytest.mark.parametrize('fault', ['saved-version', 'saved-owner', 'saved-order', 'cotangent-tid', 'output-order', 'bool-version', 'cotangent-initial', 'source-cid', 'source-name'])
def test_actual_source_role_identity_rejected_at_new_boundary(captured, fault):
    bind = api()
    for original, index in captured:
        # Fresh unchanged predecessor accepts. Only the new boundary is invoked
        # after mutation; an upstream emitter rejection cannot satisfy this test.
        bind(original, index)
        cells = list(original)
        cell = object.__new__(type(cells[index]))
        for slot in cell.__slots__:
            setattr(cell, slot, getattr(cells[index], slot))
        cells[index] = cell
        bind(cells, index)  # clone itself preserves all transient source authority
        cell.inputs = list(cell.inputs); cell.outputs = list(cell.outputs)
        if fault == 'saved-version': cell.inputs[1] = cell.inputs[1]._replace(v=cell.inputs[1].v+1)
        elif fault == 'saved-owner': cell.inputs[1] = cell.inputs[1]._replace(rank=cell.rank+1)
        elif fault == 'saved-order': cell.inputs[1:] = reversed(cell.inputs[1:])
        elif fault == 'cotangent-tid': cell.inputs[0] = cell.inputs[0]._replace(tid=cell.inputs[0].tid+1)
        elif fault == 'output-order': cell.outputs.reverse()
        elif fault == 'cotangent-initial': cell.inputs[0] = cell.inputs[0]._replace(v=0)
        elif fault == 'source-cid': cell.node = cell.node._replace(cid=cell.node.cid+1)
        elif fault == 'source-name': cell.node = cell.node._replace(irname='BW.matmul')
        else: cell.inputs[1] = cell.inputs[1]._replace(v=True)
        with pytest.raises(ValueError, match='bw-linear .*identity'):
            bind(cells, index)


@pytest.mark.parametrize('fault', ['saved-ir', 'grad-ir', 'dx-ir', 'weight-value', 'cotangent-version', 'suffix-write'])
def test_actual_mirror_ir_and_read_versions_not_dto_authority(captured, fault):
    bind = api()
    for original, index in captured:
        cells = list(original)
        cell = object.__new__(type(cells[index]))
        for slot in cell.__slots__:
            setattr(cell, slot, getattr(cells[index], slot))
        cells[index] = cell
        bind(cells, index)
        cell._input_irs = list(cell._input_irs); cell._output_irs = list(cell._output_irs)
        cell.inputs = list(cell.inputs)
        if fault in ('saved-ir', 'grad-ir'):
            port = 1 if fault == 'saved-ir' else 0
            # Coordinated DTO ref+IR change: still shaped correctly, but not
            # the original mirror's input/gradient.
            ir = copy.deepcopy(cell._input_irs[port]); ir._id += 10000
            cell._input_irs[port] = ir
            cell.inputs[port] = cell.inputs[port]._replace(tid=ir.tid)
        elif fault == 'dx-ir':
            cell._output_irs = list(reversed(cell._output_irs))
            cell.outputs = list(reversed(cell.outputs))
        elif fault == 'weight-value':
            ir = copy.deepcopy(cell._input_irs[2]); ir._valmap = type(ir._valmap)((1, 3))
            cell._input_irs[2] = ir
        elif fault == 'cotangent-version':
            cell.inputs[0] = cell.inputs[0]._replace(v=cell.inputs[0].v+1)
        else:
            suffix = object.__new__(type(cell))
            for slot in cell.__slots__:
                setattr(suffix, slot, getattr(cell, slot))
            suffix.outputs = [cell.inputs[1]]
            cells.append(suffix)
        with pytest.raises(ValueError, match='bw-linear'):
            bind(cells, index)
