"""Original source embedding producer equations on the same final Stores."""
import importlib
import importlib.util
import pytest
from scripts.tests.test_runtime_input_relations import fed
from Verdict import graph_to_lean as c
from scripts.tests.test_graph_to_lean_runtime_lineage import fixture


def setup(root, units=2,tp=2):
    world,lineages=fed(root,units,tp)
    sm,pm,_=fixture(units,tp)
    sv,pv=c._lower_runtime_graphs(sm,pm)
    return world,lineages,sv,pv


def api():
    assert importlib.util.find_spec('Verdict.runtime_embedding_values'), 'embedding source producer renderer missing'
    return importlib.import_module('Verdict.runtime_embedding_values').render


@pytest.mark.parametrize('units,tp',[(1,1),(2,2),(3,2)])
def test_emits_original_producers_and_structural_operand_guards(tmp_path,units,tp):
    world,lineages,sm,pm=setup(tmp_path,units,tp)
    text,detail=api()(sm,pm,lineages,world.receipt['execution_order'])
    assert len(detail['reads'])==1+units*tp
    assert text.count('SourceEmbeddingRead.embedding_value_of_split')==1+units*tp
    assert '.drop ' in text and '∀ row ∈' in text
    assert detail['proof_admissible'] is False
    assert detail['torch_refinement'] is False


def test_operand_written_later_cannot_be_assumed_live(tmp_path):
    import copy
    world,lineages,sm,pm=setup(tmp_path)
    order=copy.deepcopy(world.receipt['execution_order'])
    # Move the input producer after its embedding consumer: not a valid source
    # schedule. The local structural guard must also reject this mutation.
    seq=order['sm']['execution_to_source']
    seq[0],seq[1]=seq[1],seq[0]
    with pytest.raises(ValueError,match='operand.*written'):
        api()(sm,pm,lineages,order)
