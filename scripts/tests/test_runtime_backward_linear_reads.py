"""BW source-read fragment over the actual original expanded capture graph."""
import importlib
import importlib.util

import pytest

from scripts.tests.test_backward_linear_authority import captured


@pytest.fixture(scope='module')
def worlds(captured):
    from nnscaler_backend.build_graph import _emit_graph, _fuse_collective_inputs
    from nnscaler_backend.dfg import NNScalerDFG
    from nnscaler_backend.runtime_source_authority import export_expanded_cells
    from Verdict.graph_to_lean import _lower_runtime_graphs
    from Verdict.runtime_schedule import build
    # Recover World from the trusted capture rather than infer DP semantics from
    # rank counts. `captured` contains each rank's raw preparation exactly once.
    import os, json, pickle
    from pathlib import Path
    from verdict.graph import World, WType
    result=[]
    for name,label in [('global-b2','s'),('p2-r4','p')]:
        path=Path(os.environ['TRAINVERIFY_CAPTURE_ROOT'])/name/'capture.pkl'
        with path.open('rb') as stream: mg=pickle.load(stream)
        world=World(wtype=WType(label),plan_ndevs=len(mg.devices),runtime_ndevs=mg.runtime_ndevs,
                    **json.loads(path.with_suffix('.json').read_text()))
        cells=[c for rows,_ in captured for c in rows if c.node.wtype==label]
        cells,_=_fuse_collective_inputs(cells)
        graph=NNScalerDFG(world); _emit_graph(graph,cells)
        snapshot=export_expanded_cells(world,cells)
        result.append((graph,cells,snapshot,'sm' if label=='s' else 'pm'))
    views=_lower_runtime_graphs(*(row[0] for row in result))
    return [(view,cells,snapshot,build(view),label)
            for view,(_,cells,snapshot,label) in zip(views,result,strict=True)]


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_linear_reads'), 'missing original BW read fragment'
    return importlib.import_module('Verdict.runtime_backward_linear_reads').render_read


def test_actual_original_bw_reads_use_complete_execution_suffix(worlds):
    render=api()
    for view,cells,snapshot,order,label in worlds:
        index=next(i for i,c in enumerate(cells) if c.opname.name=='BW_linear')
        text,row=render(view,cells,snapshot,index,order,label)
        cell=cells[index]
        assert row['source_index']==index
        assert row['execution_index']==order['source_to_execution'][index]
        assert row['input_refs']==[list(t) for t in cell.inputs]
        assert row['output_refs']==[list(t) for t in cell.outputs]
        assert row['operand_nonwrite_source_indices']==order['execution_to_source'][row['execution_index']:]
        assert 'SourceBWLinearRead.bw_linear_dx_value_of_split' in text
        assert 'SourceBWLinearRead.bw_linear_dw_value_of_split' in text
        assert len(row['theorems'])==2
        assert row['source_contract']['saved_inputs']==[list(t) for t in cell.inputs[1:]]
        assert all(row[k] is False for k in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'))


def test_empty_source_params_are_not_inferred_from_fw_name(worlds, monkeypatch):
    from Verdict import graph_to_lean
    render=api()
    args=worlds[0]; view,cells,snapshot,order,label=args
    index=next(i for i,c in enumerate(cells) if c.opname.name=='BW_linear')
    render(view,cells,snapshot,index,order,label)
    monkeypatch.setattr(graph_to_lean,'_get_node_params',lambda *a,**k: [False])
    with pytest.raises(ValueError,match='bw-linear .*params'):
        render(view,cells,snapshot,index,order,label)


@pytest.mark.parametrize('fault',['call','export','saved-order','fw-writer-missing','duplicate','execution-order'])
def test_join_rejects_tampered_export_after_fresh_raw_bind(worlds,fault):
    import copy
    from trainverify.backward_linear_authority import bind
    render=api()
    for view,cells,snapshot,order,label in worlds:
        index=next(i for i,c in enumerate(cells) if c.opname.name=='BW_linear')
        _,good=render(view,cells,snapshot,index,order,label)
        source=copy.deepcopy(snapshot); execution=copy.deepcopy(order)
        row=next(w for w in source['writers'] if w['export_id']==good['bw_writer'])
        if fault=='call': row['ref']['call_instance']+=1
        elif fault=='export': row['export_id']='wrong'
        elif fault=='saved-order': row['inputs'][1:]=reversed(row['inputs'][1:])
        elif fault=='fw-writer-missing': source['writers']=[w for w in source['writers'] if w['export_id']!=good['fw_writer']]
        elif fault=='duplicate': source['writers'].append(copy.deepcopy(row))
        else: execution['execution_to_source'].reverse()
        bind(cells,index)  # raw source predecessor is still good
        with pytest.raises(ValueError): render(view,cells,source,index,execution,label)


@pytest.mark.parametrize('fault', ['source-signature','forward-lowered-op'])
def test_source_function_and_forward_lowering_are_independent_authorities(worlds, monkeypatch, fault):
    from verdict.operators.names import OpName
    render=api()
    for view,cells,snapshot,order,label in worlds:
        index=next(i for i,c in enumerate(cells) if c.opname.name=='BW_linear')
        _,good=render(view,cells,snapshot,index,order,label)
        fw=cells[good['source_contract']['fw_source_index']]
        with monkeypatch.context() as m:
            if fault=='source-signature':
                assert fw.ir.signature=='torch.nn.functional.linear'
                m.setattr(fw.ir,'signature','torch.mul')
            else:
                m.setitem(view.source._node2opname,fw.node,OpName.FW_mul)
            with pytest.raises(ValueError,match='bw-linear'):
                render(view,cells,snapshot,index,order,label)
        assert render(view,cells,snapshot,index,order,label)[1]==good
