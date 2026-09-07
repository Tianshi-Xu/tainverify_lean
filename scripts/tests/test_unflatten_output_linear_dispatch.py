"""Dispatch/import coverage for mixed view-unflatten and output-linear frames."""
import pytest
from trainverify.bridge_emitter.compound_rule_dispatch import select_compound_renderer
from trainverify.bridge_emitter.closed_segment_import_policy import plan_closed_segment_imports

VIEW='fw-view-unflatten-sequence-sharded-k-rank'
LINEAR='linear-output-sharded-k-rank'
BINDING='unflatten_output_linear_renderer:render_closed_unflatten_output_linear_segment'

@pytest.mark.parametrize('family',[(VIEW,LINEAR,LINEAR),(LINEAR,VIEW,LINEAR),(VIEW,VIEW,LINEAR)])
def test_mixed_unflatten_output_linear_dispatch(family):
    assert select_compound_renderer(family)==BINDING
    imports=plan_closed_segment_imports(family,(
        'TrainVerify.Denote.fw_view_unflatten_allGather_dim1_rank3',
        'TrainVerify.Denote.fw_linear_3d_weight_allGatherPrimDimN_dim0_comm'))
    assert 'denote.KRankViewUnflatten' in imports
    assert 'denote.KRankLinearGather' in imports

@pytest.mark.parametrize('family',[(VIEW,),(LINEAR,),(VIEW,'joined-to-unary'),(VIEW,LINEAR,'unknown-rule')])
def test_unrelated_families_not_absorbed(family):
    assert select_compound_renderer(family)!=BINDING
