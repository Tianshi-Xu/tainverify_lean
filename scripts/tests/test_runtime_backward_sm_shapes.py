"""Sparse SM shape projection over unchanged, original captured worlds."""
import importlib
import importlib.util
import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_sm_shapes'), 'missing sparse SM shape projection API'
    return importlib.import_module('Verdict.runtime_backward_sm_shapes')


def test_actual_sparse_chain_closes_from_original_view_and_input_reads(worlds):
    text, detail = api().render(worlds)
    assert detail['source_indices'] == [0,1,2,3,4,23,24,25,26,27,28,29,30,31,32,51,52,53,54,55,56,57,58,59,60,61,63]
    assert detail['view_anchors'] == [23,51]
    assert {p['tid'] for p in detail['parameter_shapes']} == {1212,1213,1219,1222,1223,1229,1232,1233,1236}
    assert [(r['tid'],r['shape']) for r in detail['conclusions']] == [(1318,[2,16,64]),(1319,[2,16,256]),(1375,[2,16,256])]
    assert 'SourceLayoutRead.view_value_of_split' in text
    assert 'SourceInitialInputRead.input_value_of_split' in text
    assert 'SourceBWSumRead.bw_sum_value_of_split' in text
    assert 'backwardSMFinalParameterShapes t' in text
    assert 'smDenoteWithInputs s = some t' in text
    assert 'PrefixRun' not in text and 'native_decide' not in text
    assert all(detail[k] is False for k in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'))


@pytest.mark.parametrize('fault', ['signature','raw-kwargs','params','writer','ordered-refs','execution','output-shape','sum-mirror','scope'])
def test_fresh_original_binding_rejects_after_positive_control(worlds, monkeypatch, fault):
    from Verdict import graph_to_lean
    render=api().render
    _,good=render(worlds)
    view,cells,snapshot,order,label=worlds[0]
    with monkeypatch.context() as m:
        selected=51
        if fault=='signature': m.setattr(cells[selected].ir,'signature','torch.mul')
        elif fault=='raw-kwargs':
            m.setattr(cells[selected],'kwargs',dict(cells[selected].kwargs, size=(2,8,128)))
        elif fault=='params':
            original=graph_to_lean._get_node_params
            m.setattr(graph_to_lean,'_get_node_params',lambda v,n,**kw: [2,8,128] if n==cells[selected].node else original(v,n,**kw))
        elif fault=='writer':
            row=next(w for w in snapshot['writers'] if w['export_id']==next(r['writer'] for r in good['reads'] if r['source_index']==selected))
            m.setitem(row,'export_id','tampered')
        elif fault=='ordered-refs':
            m.setattr(cells[53],'inputs',list(reversed(cells[53].inputs)))
        elif fault=='execution':
            m.setitem(order,'execution_to_source',list(reversed(order['execution_to_source'])))
        elif fault=='output-shape':
            original=view.tensor_shape
            m.setattr(view,'tensor_shape',lambda t: (2,8,128) if t.tid==1310 else original(t))
        elif fault=='sum-mirror': m.setattr(cells[63].ir.mirror,'signature','torch.mean')
        else: m.setattr(view,'collective_scopes',{cells[selected].node: {'unsupported':True}},raising=False)
        with pytest.raises(ValueError): render(worlds)
    assert render(worlds)[1]==good


def test_shape_dependencies_stop_at_views_not_attention(worlds):
    text,detail=api().render(worlds)
    for row in detail['reads']:
        if row['op']=='FW_view':
            assert all(not x['dependencies'] for x in row['shape_outputs'].values())
        assert row['operand_nonwrite_source_indices']==worlds[0][3]['execution_to_source'][row['execution_index']:]
        assert row['writer']
    assert 'fw_linear_3d_shape' in text and 'fw_gelu_shape' in text
    assert 'SourceValueRead.node_value_of_split' in text
    assert 'hp1318' not in text and 'hp1375' not in text
    assert 'smNode_50 ' not in text
    assert 'smNode_0_contract (by decide)' not in text  # Tensor membership is not decidable


def test_coordinated_dto_view_writer_permutation_still_rejected_by_raw_ir(worlds,monkeypatch):
    view,cells,snapshot,_,_=worlds[0]
    text,good=api().render(worlds)
    row=next(r for r in good['reads'] if r['op']=='FW_add')
    cell=cells[row['source_index']]; node=cell.node
    writer=next(r for r in snapshot['writers'] if r['export_id']==row['writer'])
    original_inputs=tuple(cell.ir.inputs())
    with monkeypatch.context() as m:
        m.setattr(cell,'inputs',list(reversed(cell.inputs)))
        m.setattr(cell,'_input_irs',list(reversed(cell._input_irs)))
        m.setitem(view._node2inputs,node,list(reversed(view.node_inputs(node))))
        m.setitem(view.source._node2inputs,node,list(reversed(view.source.node_inputs(node))))
        m.setitem(writer,'inputs',list(reversed(writer['inputs'])))
        assert tuple(cell.ir.inputs())==original_inputs
        with pytest.raises(ValueError,match='original ordered IR metadata mismatch'):
            api().render(worlds)
    assert api().render(worlds)==(text,good)
