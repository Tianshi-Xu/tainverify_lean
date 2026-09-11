"""Fresh original BW_layernorm authority; three separate same-final-store reads."""
import importlib
import importlib.util
import pytest
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds


def api():
    assert importlib.util.find_spec('Verdict.runtime_backward_layernorm_reads'), 'missing original BW_layernorm reader'
    return importlib.import_module('Verdict.runtime_backward_layernorm_reads')


def selected(worlds):
    for view,cells,snapshot,order,label in worlds:
        ranks=dict.fromkeys(c.rank for c in cells)
        for rank in ranks:
            i=next(i for i in order['execution_to_source'] if cells[i].rank==rank and cells[i].opname.name=='BW_layernorm')
            yield view,cells,snapshot,i,order,label


def test_original_layernorm_three_output_reads(worlds):
    rows=[]
    for args in selected(worlds):
        text,row=api().render_read(*args); rows.append(row)
        assert row['source_contract']['input_roles']==['cotangent','saved_input','saved_gamma','saved_beta']
        assert row['source_contract']['output_roles']==['dx','dgamma','dbeta']
        assert len(row['theorems'])==3
        assert all('bw_layernorm_'+role+'_value_of_split' in text for role in ('dx','dgamma','dbeta'))
        assert '(bw_layernorm ' in text and ').2.1' in text and ').2.2' in text
        assert row['source_contract']['epsilon']==1e-5
        assert row['operand_nonwrite_source_indices']==args[4]['execution_to_source'][row['execution_index']:]
        assert all(row[k] is False for k in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'))
    assert [(r['world'],r['source_index'],r['execution_index']) for r in rows]==[('sm',65,65),('pm',111,221),('pm',347,224),('pm',583,643),('pm',819,646)]


@pytest.mark.parametrize('fault',['signature','epsilon','normalized-shape','saved-version','saved-order','gradient-order','coordinated-gradient-order','gamma-metadata','cotangent-initial','fw-lowered-op','params','writer-call','suffix'])
def test_original_ln_boundary_rejects_after_positive_control(worlds,monkeypatch,fault):
    import copy
    from verdict.operators.names import OpName
    for args in selected(worlds):
        view,cells,snapshot,i,order,label=args
        text,good=api().render_read(*args)
        cell=cells[i]; fw=cells[good['source_contract']['fw_source_index']]
        with monkeypatch.context() as m:
            if fault=='signature': m.setattr(fw.ir,'signature','torch.nn.functional.batch_norm')
            elif fault in ('epsilon','normalized-shape'):
                key='eps' if fault=='epsilon' else 'normalized_shape'
                value=1e-4 if fault=='epsilon' else (2,64)
                for obj in (cell,fw):
                    m.setattr(obj,'kwargs',dict(obj.kwargs,**{key:value}))
                    m.setitem(obj.ir.kwargs,key,value)
            elif fault=='saved-version': m.setattr(cell,'inputs',[cell.inputs[0],cell.inputs[1]._replace(v=cell.inputs[1].v+1),*cell.inputs[2:]])
            elif fault=='saved-order': m.setattr(cell,'inputs',[cell.inputs[0],*reversed(cell.inputs[1:])])
            elif fault in ('gradient-order','coordinated-gradient-order'):
                m.setattr(cell,'outputs',[cell.outputs[0],cell.outputs[2],cell.outputs[1]])
                if fault=='coordinated-gradient-order': m.setattr(cell,'_output_irs',[cell._output_irs[0],cell._output_irs[2],cell._output_irs[1]])
            elif fault=='gamma-metadata':
                ir=copy.deepcopy(cell._input_irs[2]); ir._valmap=type(ir._valmap)((1,3))
                m.setattr(cell,'_input_irs',[*cell._input_irs[:2],ir,cell._input_irs[3]])
            elif fault=='cotangent-initial': m.setattr(cell,'inputs',[cell.inputs[0]._replace(v=0),*cell.inputs[1:]])
            elif fault=='fw-lowered-op': m.setitem(view.source._node2opname,fw.node,OpName.FW_gelu)
            elif fault=='params':
                from Verdict import graph_to_lean
                m.setattr(graph_to_lean,'_get_node_params',lambda *a,**k:[False])
            elif fault=='writer-call':
                row=next(w for w in snapshot['writers'] if w['export_id']==good['bw_writer'])
                m.setitem(row['ref'],'call_instance',row['ref']['call_instance']+1)
            else:
                later=cells[order['execution_to_source'][-1]]
                m.setattr(later,'outputs',[cell.inputs[1]])
            with pytest.raises(ValueError): api().render_read(*args)
        assert api().render_read(*args)==(text,good)
