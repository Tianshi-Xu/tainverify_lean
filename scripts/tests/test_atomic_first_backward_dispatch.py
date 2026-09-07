import pytest
from trainverify.bridge_emitter.composer import render_closed_segment
from trainverify.bridge_emitter.closed_segment_import_policy import plan_closed_segment_imports

@pytest.mark.parametrize('tag,k', [('Sum',k) for k in (1,2,3,4)]+[('SeqA',k) for k in (2,3,4)]+[('GeluW',k) for k in (2,3,4)])
def test_exact_kernel_witness_bytes(tag,k):
    from pathlib import Path
    from scripts.tests.sum_fw_bw_witness import witness_source as a
    from scripts.tests.bw_sequence_linear_alltoall_witness import witness_source as b
    from scripts.tests.bw_gelu_wred_witness import witness_source as c
    source={'Sum':a,'SeqA':b,'GeluW':c}[tag](k)
    file=Path(__file__).resolve().parents[2]/'trainverify'/'denote'/f'GeneratedAtomic{tag}K{k}.lean'
    assert file.read_text()==source

@pytest.mark.parametrize('tag',('sum','sequence','gelu'))
def test_first_backward_compound_dispatch(tag):
    if tag=='sum':
        from scripts.tests.sum_fw_bw_witness import fixture
        from trainverify.bridge_emitter.sum_fw_bw_renderer import render_closed_sum_fw_bw_segment as direct
        required={'denote.KRankBWSumSequence'}
    elif tag=='sequence':
        from scripts.tests.bw_sequence_linear_alltoall_witness import renderer_fixture as fixture
        from trainverify.bridge_emitter.bw_sequence_linear_alltoall_renderer import render_closed_bw_sequence_linear_alltoall_segment as direct
        required={'denote.KRankBWLinearDwSequenceGeneral','denote.KRankBWLinearDxSequence'}
    else:
        from scripts.tests.bw_gelu_wred_witness import fixture
        from trainverify.bridge_emitter.bw_gelu_wred_renderer import render_closed_bw_gelu_wred_segment as direct
        required=set()
    ir,rel=fixture(3);sid=rel.dependent_chain_plan.segments[0].segment_id
    expected=direct(ir,rel,sid)
    assert render_closed_segment(ir,rel,sid)==expected
    assert required<=set(plan_closed_segment_imports(tuple(t.rule_id for t in rel.transition_specs),tuple(t.lean_theorem for t in rel.transition_specs)))
