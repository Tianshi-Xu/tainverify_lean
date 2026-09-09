"""Ordered source list slices must produce actual input Tensor equalities."""
import copy
import importlib
import importlib.util
import pytest
from Verdict import graph_to_lean as c
from Verdict.runtime_lineage import trace
from Verdict.runtime_world import render
from Verdict.runtime_input_feed import bind
from scripts.tests.test_graph_to_lean_runtime_lineage import fixture
from scripts.tests.test_runtime_input_feed import observed


def fed(root, units=2, tp=2):
    sm, pm, original = fixture(units, tp)
    inputs = (*original[:2], *observed(root, units, tp))
    sv, pv = c._lower_runtime_graphs(sm, pm)
    lineages, _, _ = trace(sv, pv, *inputs)
    world = bind(render(sv,pv,*inputs[:2]),sv,pv,*inputs,root)
    return world, lineages


def api():
    assert importlib.util.find_spec('Verdict.runtime_input_relations'), 'input Tensor relation renderer missing'
    return importlib.import_module('Verdict.runtime_input_relations').render


@pytest.mark.parametrize('units,tp', [(1,1),(2,2),(3,2)])
def test_original_feeds_emit_one_checked_slice_per_rank_port(tmp_path,units,tp):
    world, lineages = fed(tmp_path,units,tp)
    text, detail = api()(world.receipt['input_feed'],lineages)
    assert len(detail['slices']) == units*tp*2
    assert text.count('SourceInitialInputEncoding.emitted_ordered_slice_eq_chunk') == units*tp*2
    assert '(hSlices' not in text
    assert detail['kernel_value_proved'] is False
    assert detail['torch_refinement'] is False


@pytest.mark.parametrize('fault',['value','swap','version','omit','positions','shape','duplicate'])
def test_bad_feed_identity_or_ordered_values_reject(tmp_path,fault):
    from dataclasses import replace
    world,lineages=fed(tmp_path)
    feed=copy.deepcopy(world.receipt['input_feed'])
    pms=[r for r in feed['loaders'] if r['world']=='pm']
    if fault=='value':pms[0]['ports'][0]['values'][0]+=1
    elif fault=='swap':pms[0]['ports'][0]['values'],pms[2]['ports'][0]['values']=pms[2]['ports'][0]['values'],pms[0]['ports'][0]['values']
    elif fault=='version':pms[0]['ports'][0]['ref']['version']+=1
    elif fault=='omit':pms[0]['ports'].pop()
    elif fault=='shape':pms[0]['ports'][0]['shape']=[999,1]
    elif fault=='duplicate':pms[0]['ports'].append(pms[0]['ports'][0])
    else:
        row=lineages[0]
        lineages=(replace(row,units=tuple(reversed(row.units))),*lineages[1:])
    with pytest.raises(ValueError):api()(feed,lineages)
