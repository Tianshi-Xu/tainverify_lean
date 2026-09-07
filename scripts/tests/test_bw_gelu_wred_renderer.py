import importlib.util
from scripts.tests.bw_gelu_wred_witness import fixture


def test_valid_atomic_backend():
    ir, relation = fixture()
    assert relation.certificates[1].input_fact != relation.certificates[0].output_fact
    name = "trainverify.bridge_emitter.bw_gelu_wred_renderer"
    assert importlib.util.find_spec(name) is not None, "C03 atomic backend is missing"
    from trainverify.bridge_emitter.bw_gelu_wred_renderer import render_closed_bw_gelu_wred_segment
    source = render_closed_bw_gelu_wred_segment(ir, relation, "segment_000000")
    assert "bw_gelu_allGatherPrimDimN_eq" in source
    assert "cross_dp_wred_eq_allReducePrim" in source
    assert "ClosedDepSegmentCertificate" in source
    assert source.count("apply RelationState.Holds.fold_frame") == 1


from dataclasses import replace
import pytest
from scripts.tests.bw_gelu_wred_witness import witness_source
from trainverify.bridge_emitter.bw_gelu_wred_renderer import render_closed_bw_gelu_wred_segment as render
from trainverify.bridge_emitter.composer import _typed_certificate_digest


@pytest.mark.parametrize("k", [2,3,4])
@pytest.mark.parametrize("dim,shard", [(0,(2,5)),(1,(3,2,7))])
def test_generated_witness(k,dim,shard):
    source = witness_source(k,dim=dim,shard=shard,collision=True)
    assert source == witness_source(k,dim=dim,shard=shard,collision=True)
    assert source.count("private theorem segment_000000_hPmWriter") == k
    assert source.count("apply RelationState.Holds.fold_frame") == 1
    assert "axiom " not in source and "sorry" not in source


@pytest.mark.parametrize("mutation", ["source_axis","source_tid","stale_ref","ordered_tids","shape","retired","anchor","overwrite","rank","certificate_shape","duplicate","internal"])
def test_coherent_mutation_after_valid_baseline(mutation):
    ir,rel=fixture(3)
    assert render(ir,rel,"segment_000000")
    chain=rel.dependent_chain_plan
    if mutation in {"source_axis","source_tid","stale_ref"}:
        f=chain.relation_facts[0]
        if mutation=="source_axis": src=replace(f.source,gather_dim=0)
        elif mutation=="source_tid": src=replace(f.source,step_triple=("init:999",*f.source.step_triple[1:]))
        else:
            ir.sm_nodes.insert(0, __import__("trainverify.bridge_emitter.parser",fromlist=["Node"]).Node(0,"FW_contiguous",[88],[10],[]))
            chain.segments=(replace(chain.segments[0],sm_range=(1,2)),)
            c=replace(rel.certificates[0],sm_step_id="sm:1:0",output_fact=replace(rel.certificates[0].output_fact,step_triple=("sm:1:0",*rel.certificates[0].output_fact.step_triple[1:])))
            rel.certificates=(c,rel.certificates[1])
            rel.transition_specs=(replace(rel.transition_specs[0],sm_node_indices=(1,),post_facts=(c.output_fact,),certificate_digest=_typed_certificate_digest(c)),rel.transition_specs[1])
            chain.relation_facts=tuple(replace(x,source=c.output_fact) if x.fact_id=="fo" else x for x in chain.relation_facts)
            src=f.source
        c=replace(rel.certificates[0],gradient_fact=src)
        rel.certificates=(c,rel.certificates[1])
        rel.transition_specs=(replace(rel.transition_specs[0],pre_facts=tuple(sorted((src,c.activation_fact))),certificate_digest=_typed_certificate_digest(c)),rel.transition_specs[1])
        chain.relation_facts=tuple(replace(x,source=src) if x.fact_id=="fg" else x for x in chain.relation_facts)
    elif mutation=="ordered_tids": ir.pm_nodes[2].ins.reverse()
    elif mutation=="shape": chain.relation_facts=tuple(replace(f,full_shape=(999,999)) if f.kind=="sharded" else f for f in chain.relation_facts)
    elif mutation=="retired": chain.states=(chain.states[0],replace(chain.states[1],fact_ids=(*chain.states[1].fact_ids,"fw")))
    elif mutation=="anchor": chain.anchor_fact=replace(chain.anchor_fact,tid=30)
    elif mutation=="overwrite": ir.pm_nodes[-1].outs=[600]
    elif mutation=="rank": ir.pm_num_ranks=2
    elif mutation=="certificate_shape":
        c=replace(rel.certificates[1],full_shape=(99,))
        rel.certificates=(rel.certificates[0],c)
        rel.transition_specs=(rel.transition_specs[0],replace(rel.transition_specs[1],certificate_digest=_typed_certificate_digest(c)))
    elif mutation=="duplicate": rel.certificates=(*rel.certificates,rel.certificates[0])
    else: chain.states=(replace(chain.states[0],fact_ids=tuple(f for f in chain.states[0].fact_ids if f!="fw")),chain.states[1])
    with pytest.raises(ValueError): render(ir,rel,"segment_000000")


def test_witness_imports_and_namespace_are_complete():
    source=witness_source()
    assert "import denote.KRankBWGelu" not in source
    assert source.count("import denote.RelationCompiler") == 1
    assert source.index("import denote.RelationCompiler") < source.index("namespace ")
    assert "#print axioms segment_000000" in source


def test_unrelated_certificate_and_transition_order_are_neutral():
    ir,rel=fixture(4)
    original=render(ir,rel,"segment_000000")
    c=replace(rel.certificates[0],output_fact=replace(rel.certificates[0].output_fact,gather_dim=0))
    rel.certificates=(*rel.certificates,c)
    chain=rel.dependent_chain_plan
    chain.segments=(replace(chain.segments[0],transition_ids=("wred","gelu")),)
    assert render(ir,rel,"segment_000000")==original
