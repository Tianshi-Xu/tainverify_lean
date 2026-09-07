"""Keep every accepted column-dW proof tied to its current generator."""
from pathlib import Path
import pytest
from scripts.tests.bw_linear_dw_column_general_witness import CASES,witness_source,mixed_witness_source

ROOT=Path(__file__).resolve().parents[2]


@pytest.mark.parametrize('j,args',tuple(enumerate(CASES)))
@pytest.mark.parametrize('dual',(False,True))
def test_column_generated_bytes(j,args,dual):
    name=f'GeneratedBWLinearDwColumnGeneralCase{j}_{int(dual)}'
    assert (ROOT/f'trainverify/denote/{name}.lean').read_text()==witness_source(
        *args,dual=dual,sparse=True,with_view=True,namespace=f'ColumnDwCase{j}_{int(dual)}')


def test_column_mixed_generated_bytes():
    assert (ROOT/'trainverify/denote/GeneratedBWLinearDwColumnMixedGeneralWitness.lean').read_text()==mixed_witness_source()


@pytest.mark.parametrize('rule,theorem,module',[
    ('bw-linear-dw-input-column-sharded-k-rank','bw_linear_dw_column_allGather_rank3','KRankBWLinearDwColumnGeneral'),
    ('bw-linear-dw-output-row-sharded-k-rank','bw_linear_dw_row_allGather_rank3','KRankBWLinearDwRowGeneral'),
    ('bw-linear-dw-sequence-reduction-k-rank','bw_linear_dw_sequence_reduction_rank3','KRankBWLinearDwSequenceGeneral'),
])
def test_compound_dw_theorem_import(rule,theorem,module):
    from trainverify.bridge_emitter.closed_segment_import_policy import plan_closed_segment_imports
    from trainverify.bridge_emitter.relation_compiler import CLOSED_RULE_REGISTRY
    imports=plan_closed_segment_imports((rule,'bw-view-joined'),
        ('TrainVerify.Denote.'+theorem,'TrainVerify.Denote.RelationCompiler.JoinedRel.fw_view'),CLOSED_RULE_REGISTRY)
    assert 'denote.'+module in imports
