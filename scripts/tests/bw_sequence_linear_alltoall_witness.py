"""Portable C02 authority: shared sequence projections and independent AllToAll."""
from dataclasses import replace
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.composer import _typed_certificate_digest
from trainverify.bridge_emitter.parser import Node
from scripts.tests.bw_linear_dw_sequence_witness import renderer_fixture as dual_fixture

A_RULE = "alltoall-k-rank-layout-transport"
A_THEOREM = "TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn"


def renderer_fixture(k=3,b=2,s=5,o=7,i=11):
    ir,rel=dual_fixture(k,b,s,o,i,dual=True)
    chain=rel.dependent_chain_plan
    # Place the entire independent collective between the penultimate and last rank.
    positions=tuple(range(k-1,2*k-1))
    linear_positions=(*range(k-1),2*k-1)
    for r in range(k):
        ir.pm_nodes.insert(k-1+r,Node(r,"AllToAllPrim",list(range(7000,7000+k)),[8000+r],[1,2]))
    certs=[];ts=[];sources={}
    for t,c in zip(rel.transition_specs,rel.certificates):
        slot=1 if t.rule_id.startswith("bw-linear-dw") else 0
        out=replace(c.output_fact,step_triple=(f"sm:0:{slot}",*(f"pm:{p}:{slot}" for p in linear_positions)))
        sources[c.output_fact]=out
        c=replace(c,output_fact=out,pm_step_ids=tuple(f"pm:{p}:{slot}" for p in linear_positions))
        certs.append(c);ts.append(replace(t,post_facts=(out,),pm_node_indices=linear_positions,certificate_digest=_typed_certificate_digest(c)))
    pre=rc.RelationFactSpec("sharded",("init:700",*(f"init:{u}" for u in range(7000,7000+k))),gather_dim=1)
    post=rc.RelationFactSpec("sharded",("init:700",*(f"pm:{p}:0" for p in positions)),gather_dim=2)
    template=chain.relation_facts[0]
    a=replace(template,fact_id="fact_a_in",source=pre,sm_tid=700,pm_tids=tuple(range(7000,7000+k)),full_shape=(b,s*k,i*k),shard_shape=(b,s,i*k))
    z=replace(a,fact_id="fact_a_out",source=post,gather_dim=2,pm_tids=tuple(range(8000,8000+k)),shard_shape=(b,s*k,i))
    c=rc.KRankAllToAllRelationCertificate(A_RULE,k,1,2,pre,post,tuple(f"pm:{p}:0" for p in positions),A_THEOREM)
    ts.append(replace(ts[0],transition_id="transition_a",rule_id=A_RULE,pre_facts=(pre,),post_facts=(post,),sm_node_indices=(),pm_node_indices=positions,lean_theorem=A_THEOREM,certificate_digest=_typed_certificate_digest(c)))
    certs.append(c)
    chain.relation_facts=tuple(replace(r,source=sources.get(r.source,r.source)) for r in chain.relation_facts)+(a,z)
    chain.states=(replace(chain.states[0],fact_ids=(*chain.states[0].fact_ids,a.fact_id)),replace(chain.states[1],fact_ids=(*chain.states[1].fact_ids,a.fact_id,z.fact_id)))
    chain.segments=(replace(chain.segments[0],transition_ids=tuple(t.transition_id for t in ts),pm_range=(0,2*k)),)
    rel.certificates=tuple(certs);rel.transition_specs=tuple(ts)
    ir.sm_graph_ref="SequenceLinearAllToAll.smGraph";ir.pm_graph_ref="SequenceLinearAllToAll.pmGraph"
    return ir,rel


def witness_source(k=3):
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    from trainverify.bridge_emitter.bw_sequence_linear_alltoall_renderer import render_closed_bw_sequence_linear_alltoall_segment
    ir,rel=renderer_fixture(k)
    return fixture_source(ir,rel,render_closed_bw_sequence_linear_alltoall_segment,pm_num_ranks=k).replace("SyntheticBWLayernorm","SequenceLinearAllToAll").replace("import denote.KRankBWLayernorm","import denote.KRankBWLinearDwSequenceGeneral\nimport denote.KRankBWLinearDxSequence")
