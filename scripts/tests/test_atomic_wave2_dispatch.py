import importlib
from pathlib import Path
import pytest
from trainverify.bridge_emitter.composer import render_closed_segment
from trainverify.bridge_emitter.closed_segment_import_policy import plan_closed_segment_imports
CASES=[('SoftRS','bw_softmax_reduce_scatter','fixture',{'denote.KRankBWSoftmaxGeneral'}),('TransA','transpose_alltoall','renderer_fixture',{'denote.KRankTranspose','denote.KRankTranspose23Extra'}),('LnW','bw_layernorm_wred','fixture',{'denote.KRankBWLayernorm','denote.KRankBWLayernormParam'}),('ARS','alltoall_reduce_scatter','renderer_fixture',set()),('SoftT','bw_softmax_transpose','renderer_fixture',{'denote.KRankBWSoftmaxGeneral','denote.KRankTranspose'}),('FlatAD','bw_flatten_alltoall_div','renderer_fixture',{'denote.KRankViewFlatten'})]
@pytest.mark.parametrize('label,stem,fixture,imports',CASES)
def test_dispatch_and_exact_imports(label,stem,fixture,imports):
    mod=importlib.import_module('scripts.tests.'+stem+'_witness')
    ir,rel,*_=getattr(mod,fixture)(3);sid=rel.dependent_chain_plan.segments[0].segment_id
    backend=importlib.import_module('trainverify.bridge_emitter.'+stem+'_renderer')
    assert render_closed_segment(ir,rel,sid)==getattr(backend,'render_closed_'+stem+'_segment')(ir,rel,sid)
    ts=rel.transition_specs
    assert imports<=set(plan_closed_segment_imports(tuple(t.rule_id for t in ts),tuple(t.lean_theorem for t in ts)))
@pytest.mark.parametrize('label,stem,fixture,imports',CASES)
@pytest.mark.parametrize('k',[2,3,4])
def test_exact_kernel_bytes(label,stem,fixture,imports,k):
    mod=importlib.import_module('scripts.tests.'+stem+'_witness')
    assert (Path(__file__).resolve().parents[2]/f'trainverify/denote/GeneratedAtomic{label}K{k}.lean').read_text()==mod.witness_source(k)
