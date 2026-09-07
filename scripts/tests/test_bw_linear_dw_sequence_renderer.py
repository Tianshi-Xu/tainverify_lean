from dataclasses import replace
import importlib
import pytest
from scripts.tests.bw_linear_dw_sequence_witness import CASES,THEOREM,renderer_fixture,witness_source


def render(ir,rel):
    try: module=importlib.import_module("trainverify.bridge_emitter.bw_linear_dw_sequence_renderer")
    except ModuleNotFoundError: pytest.fail("positive sequence dW renderer is not implemented")
    return module.render_closed_bw_linear_dw_sequence_segment(ir,rel,"segment_000000")


@pytest.mark.parametrize("args",CASES)
@pytest.mark.parametrize("dual",(False,True))
def test_positive_generic_sequence_dw(args,dual):
    ir,rel=renderer_fixture(*args,dual=dual,sparse=True)
    source=render(ir,rel)
    assert THEOREM in source
    assert source.count("private def segment_000000_sm_final") == 1
    assert source.count("private def segment_000000_pm_final") == 1
    assert "tensorSum" in source and "9001" in source and "9011" in source
    assert ("bw_linear_dx_sequence_allGather_rank3" in source)==dual
    assert "g170" not in source and "g144" not in source
    assert "sorry" not in source and "admit" not in source


@pytest.mark.parametrize("mutation",("rank","header","params","tupleparams","pairing","shape","axis","source","weightaxis","digest","duplicate","frame","roles","projection"))
def test_fail_closed(mutation):
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    ir,rel=renderer_fixture(dual=True,sparse=True)
    chain=rel.dependent_chain_plan
    if mutation=="rank":ir.pm_nodes[2].rank=0
    if mutation=="header":ir.pm_num_ranks=4
    if mutation=="params":ir.sm_nodes[0].params=[1]
    if mutation=="tupleparams":ir.sm_nodes[0].params=()
    if mutation=="pairing":ir.pm_nodes[2].ins[0]=1000
    if mutation=="shape":chain.relation_facts=tuple(replace(r,full_shape=(2,14,7)) if r.fact_id=="fact_g" else r for r in chain.relation_facts)
    if mutation=="axis":chain.relation_facts=tuple(replace(r,source=replace(r.source,gather_dim=2)) if r.fact_id=="fact_g" else r for r in chain.relation_facts)
    if mutation=="source":chain.relation_facts=tuple(replace(r,sm_tid=101) if r.fact_id=="fact_g" else r for r in chain.relation_facts)
    if mutation=="weightaxis":chain.relation_facts=tuple(replace(r,gather_dim=1) if r.fact_id=="fact_w" else r for r in chain.relation_facts)
    if mutation=="digest":rel.transition_specs=(replace(rel.transition_specs[0],certificate_digest="bad"),*rel.transition_specs[1:])
    if mutation=="duplicate":rel.certificates=(*rel.certificates,rel.certificates[0])
    if mutation=="frame":ir.pm_nodes[1].outs=[206]
    if mutation=="roles":
        c=rel.certificates[0];c=replace(c,gradient_fact=c.activation_fact,activation_fact=c.gradient_fact)
        rel.certificates=(c,*rel.certificates[1:]);rel.transition_specs=(replace(rel.transition_specs[0],certificate_digest=_typed_certificate_digest(c)),*rel.transition_specs[1:])
    if mutation=="projection":ir.sm_nodes[0].outs.reverse()
    with pytest.raises(ValueError):render(ir,rel)


@pytest.mark.parametrize("side",("sm","pm"))
def test_input_source_cannot_name_future_writer(side):
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    from trainverify.bridge_emitter.parser import Node
    ir,rel=renderer_fixture(sparse=True)
    assert render(ir,rel)
    chain=rel.dependent_chain_plan;g=chain.relation_facts[0]
    nodes=ir.sm_nodes if side=="sm" else ir.pm_nodes
    index=len(nodes);tid=g.sm_tid if side=="sm" else g.pm_tids[0]
    nodes.append(Node(0,"FW_neg",[9900],[tid],[]))
    refs=list(g.source.step_triple);refs[0 if side=="sm" else 1]=f"{side}:{index}:0"
    source=replace(g.source,step_triple=tuple(refs))
    c=replace(rel.certificates[0],gradient_fact=source)
    rel.certificates=(c,)
    rel.transition_specs=(replace(rel.transition_specs[0],pre_facts=tuple(sorted((c.gradient_fact,c.activation_fact,c.weight_fact))),certificate_digest=_typed_certificate_digest(c)),)
    chain.relation_facts=(replace(g,source=source),*chain.relation_facts[1:])
    with pytest.raises(ValueError):render(ir,rel)


@pytest.mark.parametrize("source_ref,accepted",(("sm:1:0",True),("sm:0:0",False),("init:100",False)))
def test_latest_preceding_writer_not_stale_initial(source_ref,accepted):
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    from trainverify.bridge_emitter.parser import Node
    ir,rel=renderer_fixture()
    chain=rel.dependent_chain_plan;g=chain.relation_facts[0]
    ir.sm_nodes[:0]=[Node(0,"FW_neg",[9900],[100],[]),Node(0,"FW_neg",[9901],[100],[])]
    source=replace(g.source,step_triple=(source_ref,*g.source.step_triple[1:]))
    old=rel.certificates[0];out=replace(old.output_fact,step_triple=("sm:2:1",*old.output_fact.step_triple[1:]))
    c=replace(old,gradient_fact=source,output_fact=out,sm_step_id="sm:2:1")
    rel.certificates=(c,)
    rel.transition_specs=(replace(rel.transition_specs[0],pre_facts=tuple(sorted((source,c.activation_fact,c.weight_fact))),post_facts=(out,),sm_node_indices=(2,),certificate_digest=_typed_certificate_digest(c)),)
    chain.segments=(replace(chain.segments[0],sm_range=(2,3)),)
    chain.relation_facts=tuple(replace(r,source=source) if r.source==g.source else replace(r,source=out) if r.source==old.output_fact else r for r in chain.relation_facts)
    if accepted:assert render(ir,rel)
    else:
        with pytest.raises(ValueError,match="latest writer"):render(ir,rel)


def test_old_transpose_consumer_delegates_pure_dual():
    from trainverify.bridge_emitter.transpose_linear_transpose_renderer import render_closed_transpose_linear_transpose_segment
    ir,rel=renderer_fixture(dual=True)
    assert render_closed_transpose_linear_transpose_segment(ir,rel,"segment_000000")==render(ir,rel)


@pytest.mark.parametrize("j,args",tuple(enumerate(CASES)))
@pytest.mark.parametrize("dual",(False,True))
def test_checked_sequence_witness_bytes(j,args,dual):
    from pathlib import Path
    root=Path(__file__).resolve().parents[2]
    name=f"GeneratedBWLinearDwSequenceCase{j}_{int(dual)}"
    assert (root/f"trainverify/denote/{name}.lean").read_text()==witness_source(*args,dual=dual,sparse=True,namespace=f"SequenceDwCase{j}_{int(dual)}")


def test_witness_namespaces_and_determinism():
    from scripts.tests.bw_linear_dw_sequence_witness import combined_witness_source
    source=combined_witness_source()
    assert source==combined_witness_source()
    assert "SyntheticBWLayernorm" not in source
    assert "SyntheticBWLinearDx" not in source
    assert "maxHeartbeats 500000" in source


def test_public_dispatch_after_integration():
    from trainverify.bridge_emitter.composer import render_closed_segment
    from trainverify.bridge_emitter.relation_compiler import CLOSED_RULE_REGISTRY
    from scripts.tests.bw_linear_dw_sequence_witness import RULE
    assert RULE in CLOSED_RULE_REGISTRY
    for dual in (False,True):
        ir,rel=renderer_fixture(dual=dual)
        assert render_closed_segment(ir,rel,"segment_000000")==render(ir,rel)


@pytest.mark.parametrize("kind",("tensor_shape","tensor_eq","gather","packed_cu"))
def test_retained_anchor_and_live_authority(kind):
    from types import SimpleNamespace
    ir,rel=renderer_fixture(sparse=True)
    chain=rel.dependent_chain_plan
    anchor=SimpleNamespace(fact_id="anchor",kind=kind,side="pm",tid=9500,left_side="sm",left_tid=9501,right_side="pm",right_tid=9500,sm_tid=9501,pm_rank0_tid=9500,pm_rank1_tid=9502)
    chain.anchor_fact=anchor
    chain.states=tuple(replace(s,fact_ids=(*s.fact_ids,"anchor")) for s in chain.states)
    assert THEOREM in render(ir,rel)
    ir.pm_nodes[1].outs=[9500]
    with pytest.raises(ValueError):render(ir,rel)


def test_unrelated_exact_certificate_does_not_change_bytes():
    ir,rel=renderer_fixture()
    original=render(ir,rel)
    c=rel.certificates[0]
    rel.certificates=(*rel.certificates,replace(c,output_fact=replace(c.output_fact,step_triple=("sm:9:1","pm:9:1"))))
    assert render(ir,rel)==original


def test_top_level_import_mode(monkeypatch):
    import sys
    from pathlib import Path
    from trainverify.bridge_emitter import composer,relation_compiler
    monkeypatch.syspath_prepend(str(Path(composer.__file__).parent))
    monkeypatch.setitem(sys.modules,"composer",composer)
    monkeypatch.setitem(sys.modules,"relation_compiler",relation_compiler)
    module=importlib.import_module("bw_linear_dw_sequence_renderer")
    ir,rel=renderer_fixture()
    assert module.render_closed_bw_linear_dw_sequence_segment(ir,rel,"segment_000000")==render(ir,rel)


def test_old_dx_only_bytes_unchanged():
    import subprocess
    from pathlib import Path
    from scripts.tests.test_k_rank_bw_linear_dx_sequence import renderer_fixture as dx_fixture
    from trainverify.bridge_emitter.transpose_linear_transpose_renderer import render_closed_transpose_linear_transpose_segment
    root=Path(__file__).resolve().parents[2]
    old=subprocess.check_output(["git","show","2a9a8608:trainverify/bridge_emitter/transpose_linear_transpose_renderer.py"],cwd=root,text=True)
    ns={"__package__":"trainverify.bridge_emitter"};exec(old,ns)
    ir,rel=dx_fixture(4,1,2,32,32)
    assert ns["render_closed_transpose_linear_transpose_segment"](ir,rel,"segment_000000")==render_closed_transpose_linear_transpose_segment(ir,rel,"segment_000000")


def test_quad_consumer_new_list_abi():
    from trainverify.bridge_emitter import relation_compiler as rc
    from trainverify.bridge_emitter.parser import Node
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    from trainverify.bridge_emitter.bw_linear_matmul_quad_renderer import render_closed_bw_linear_matmul_quad_segment
    ir,rel=renderer_fixture(4,1,2,32,32,dual=True)
    chain=rel.dependent_chain_plan;template=chain.relation_facts[0]
    ins=[]
    for j in range(3):
        tids=tuple(7000+j*10+r for r in range(4))
        f=rc.RelationFactSpec("sharded",(f"init:{700+j}",*(f"init:{u}" for u in tids)),gather_dim=1)
        ins.append(replace(template,fact_id=f"mat_in{j}",source=f,sm_tid=700+j,pm_tids=tids,full_shape=(1,4,8,8),shard_shape=(1,1,8,8)))
    ir.sm_nodes.append(Node(0,"BW_matmul",[700,701,702],[710,711],[]))
    for r in range(4):ir.pm_nodes.append(Node(r,"BW_matmul",[a.pm_tids[r] for a in ins],[7100+r,7110+r],[]))
    outs=[];cs=[];ts=[]
    for slot in (0,1):
        of=rc.RelationFactSpec("sharded",(f"sm:1:{slot}",*(f"pm:{4+r}:{slot}" for r in range(4))),gather_dim=1)
        out=replace(ins[0],fact_id=f"mat_out{slot}",source=of,sm_tid=710+slot,pm_tids=tuple(7100+10*slot+r for r in range(4)))
        c=rc.KRankBWMatmulCertificate("bw-matmul-head-sharded-k-rank","head-sharded",f".{slot+1}",4,tuple(a.source for a in ins),of,f"sm:1:{slot}",tuple(f"pm:{4+r}:{slot}" for r in range(4)),f"TrainVerify.Denote.bw_matmul_{'fst' if slot==0 else 'snd'}_head_gather_rank4")
        t=replace(rel.transition_specs[0],transition_id=f"mat_t{slot}",rule_id=c.rule_id,pre_facts=tuple(sorted(c.input_facts)),post_facts=(of,),sm_node_indices=(1,),pm_node_indices=(4,5,6,7),lean_theorem=c.lean_theorem,certificate_digest=_typed_certificate_digest(c))
        outs.append(out);cs.append(c);ts.append(t)
    chain.relation_facts=(*chain.relation_facts,*ins,*outs)
    before,after=chain.states
    chain.states=(replace(before,fact_ids=(*before.fact_ids,*(a.fact_id for a in ins))),replace(after,fact_ids=(*after.fact_ids,*(a.fact_id for a in ins+outs))))
    rel.certificates=(*rel.certificates,*cs);rel.transition_specs=(*rel.transition_specs,*ts)
    chain.segments=(replace(chain.segments[0],transition_ids=tuple(t.transition_id for t in rel.transition_specs),sm_range=(0,2),pm_range=(0,8)),)
    source=render_closed_bw_linear_matmul_quad_segment(ir,rel,"segment_000000")
    assert THEOREM+" 4 1 2 32 32 [" in source
    assert "g170" not in source
    assert source.count("private def segment_000000_sm_final")==1
    ir.sm_nodes[0].ins[0]=999
    with pytest.raises(ValueError):render_closed_bw_linear_matmul_quad_segment(ir,rel,"segment_000000")
