import importlib.util
import pytest






from dataclasses import replace
from types import SimpleNamespace
from scripts.tests.bw_softmax_reduce_scatter_witness import fixture,witness_source
from trainverify.bridge_emitter.bw_softmax_reduce_scatter_renderer import render_closed_bw_softmax_reduce_scatter_segment as render
from trainverify.bridge_emitter.composer import _typed_certificate_digest

@pytest.mark.parametrize("k",[2,3,4])
@pytest.mark.parametrize("shard",[(2,3,5,7),(1,4,2,16)])
def test_portable_dynamic_witness(k,shard):
    source=witness_source(k,shard=shard,collision=True)
    assert source==witness_source(k,shard=shard,collision=True)
    assert "#print axioms segment_000000" in source
    assert source.count("apply RelationState.Holds.fold_frame")==1
    assert source.count("private theorem segment_000000_scatter_writer")==k
    assert "sorry" not in source and "axiom " not in source
    assert "import denote.RelationCompiler" in source
    from pathlib import Path
    root = Path(__file__).resolve().parents[2] / "trainverify"
    for line in source.splitlines():
        if line.startswith("import denote."):
            assert (root / (line.removeprefix("import ").replace(".", "/") + ".lean")).is_file()

@pytest.mark.parametrize("mutation",["axis","source","roles","order","shape","digest","type","duplicate","theorem","rank","anchor","active","missing","stale"])
def test_coherent_mutation_after_valid_baseline(mutation):
    ir,rel=fixture(3);assert render(ir,rel,"segment_000000")
    chain=rel.dependent_chain_plan
    if mutation in {"axis","source"}:
        f=chain.relation_facts[0]
        source=replace(f.source,gather_dim=1) if mutation=="axis" else replace(f.source,step_triple=("init:999",*f.source.step_triple[1:]))
        c=replace(rel.certificates[0],gradient_fact=source)
        rel.certificates=(c,rel.certificates[1])
        rel.transition_specs=(replace(rel.transition_specs[0],pre_facts=tuple(sorted((source,c.activation_fact))),certificate_digest=_typed_certificate_digest(c)),rel.transition_specs[1])
        chain.relation_facts=tuple(replace(x,source=source) if x.fact_id=="fg" else x for x in chain.relation_facts)
    elif mutation=="roles": ir.pm_nodes[0].ins.reverse()
    elif mutation=="order": ir.pm_nodes[2].ins.reverse()
    elif mutation=="shape":
        c=replace(rel.certificates[1],full_shape=(9,9))
        rel.certificates=(rel.certificates[0],c)
        rel.transition_specs=(rel.transition_specs[0],replace(rel.transition_specs[1],certificate_digest=_typed_certificate_digest(c)))
    elif mutation=="digest": rel.transition_specs=(replace(rel.transition_specs[0],certificate_digest="bad"),rel.transition_specs[1])
    elif mutation=="type": rel.certificates=(SimpleNamespace(**rel.certificates[0].__dict__),rel.certificates[1])
    elif mutation=="duplicate": rel.certificates=(*rel.certificates,rel.certificates[1])
    elif mutation=="theorem":
        c=replace(rel.certificates[1],lean_theorem="TrainVerify.Denote.wrong")
        rel.certificates=(rel.certificates[0],c)
        rel.transition_specs=(rel.transition_specs[0],replace(rel.transition_specs[1],lean_theorem=c.lean_theorem,certificate_digest=_typed_certificate_digest(c)))
    elif mutation=="rank": ir.pm_num_ranks=2
    elif mutation=="anchor": chain.anchor_fact=replace(chain.anchor_fact,tid=30)
    elif mutation=="active": chain.authority_facts=(replace(chain.authority_facts[0],left_tid=30),)
    elif mutation=="missing": chain.states=(replace(chain.states[0],fact_ids=tuple(x for x in chain.states[0].fact_ids if x!="fw")),chain.states[1])
    else:
        from trainverify.bridge_emitter.parser import Node
        ir.sm_nodes.insert(0,Node(0,"FW_contiguous",[88],[10],[]))
        c=replace(rel.certificates[0],sm_step_id="sm:1:0",output_fact=replace(rel.certificates[0].output_fact,step_triple=("sm:1:0",*rel.certificates[0].output_fact.step_triple[1:])))
        rel.certificates=(c,rel.certificates[1])
        rel.transition_specs=(replace(rel.transition_specs[0],sm_node_indices=(1,),post_facts=(c.output_fact,),certificate_digest=_typed_certificate_digest(c)),rel.transition_specs[1])
        chain.relation_facts=tuple(replace(f,source=c.output_fact) if f.fact_id=="fo" else f for f in chain.relation_facts)
        chain.segments=(replace(chain.segments[0],sm_range=(1,2)),)
    with pytest.raises(ValueError): render(ir,rel,"segment_000000")


def test_unrelated_certificate_order_and_retained_reduction():
    ir,rel=fixture(4);original=render(ir,rel,"segment_000000")
    rel.certificates += (replace(rel.certificates[0],output_fact=replace(rel.certificates[0].output_fact,gather_dim=0)),)
    chain=rel.dependent_chain_plan
    chain.segments=(replace(chain.segments[0],transition_ids=("scatter","soft")),)
    assert render(ir,rel,"segment_000000")==original
    chain.states=(chain.states[0],replace(chain.states[1],fact_ids=(*chain.states[1].fact_ids,"fw")))
    assert render(ir,rel,"segment_000000")
