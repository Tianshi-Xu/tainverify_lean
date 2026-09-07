import importlib
from pathlib import Path
import pytest
from trainverify.bridge_emitter.composer import render_closed_segment
from trainverify.bridge_emitter.closed_segment_import_policy import plan_closed_segment_imports
CASES=[('RowHead','bw_row_linear_head_matmul',{'denote.KRankBWLinearDwRowGeneral','denote.KRankBWLinearDxRow','denote.KRankBWMatmulHead'}),('EmbA','bw_embedding_alltoall_mixed',{'denote.BWEmbeddingHiddenShardK','denote.BWEmbeddingSequenceShardK'})]
@pytest.mark.parametrize('label,stem,imports',CASES)
def test_production_dispatch(label,stem,imports):
    m=importlib.import_module('scripts.tests.'+stem+'_witness');ir,rel,*_=m.renderer_fixture(3);sid=rel.dependent_chain_plan.segments[0].segment_id
    backend=importlib.import_module('trainverify.bridge_emitter.'+stem+'_renderer')
    assert render_closed_segment(ir,rel,sid)==getattr(backend,'render_closed_'+stem+'_segment')(ir,rel,sid)
    ts=rel.transition_specs
    assert imports<=set(plan_closed_segment_imports(tuple(t.rule_id for t in ts),tuple(t.lean_theorem for t in ts)))
@pytest.mark.parametrize('label,stem,imports',CASES)
@pytest.mark.parametrize('k',[2,3,4])
def test_exact_kernel_bytes(label,stem,imports,k):
    m=importlib.import_module('scripts.tests.'+stem+'_witness')
    assert (Path(__file__).resolve().parents[2]/f'trainverify/denote/GeneratedAtomic{label}K{k}.lean').read_text()==m.witness_source(k)
