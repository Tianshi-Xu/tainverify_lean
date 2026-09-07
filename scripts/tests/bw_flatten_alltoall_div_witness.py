"""Portable dependent AllToAll→BW_div with independent sequence BW_view."""
from dataclasses import replace
from types import SimpleNamespace
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.composer import _typed_certificate_digest
from trainverify.bridge_emitter.parser import Node
from scripts.tests.test_k_rank_bw_view_flatten import renderer_fixture as view_fixture

V_RULE='bw-view-flatten-sequence-sharded-k-rank'
A_RULE='alltoall-k-rank-layout-transport'
D_RULE='div-sharded-k-rank-dim3'
A_THEOREM='TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn'
D_THEOREM='TrainVerify.Denote.bw_div_allGatherPrimDimN_eq_g128'


def renderer_fixture(k=3,b=2,s=5,n=3,d=7,scalar=4):
    ir,rel=view_fixture(k,b,s,n,d)
    chain=rel.dependent_chain_plan
    chain.authority_facts=();chain.anchor_fact=None
    vi,vo=chain.relation_facts
    vi=replace(vi,source=replace(vi.source,step_triple=(f'init:{vi.sm_tid}',*(f'init:{u}' for u in vi.pm_tids))))
    vp=(*range(k-1),2*k-1);ap=tuple(range(k-1,2*k-1));dp=tuple(range(2*k,3*k))
    ir.sm_nodes.insert(0,Node(0,'BW_div',[700,999],[701],[scalar]))
    for r in range(k):ir.pm_nodes.insert(k-1+r,Node(r,'AllToAllPrim',list(range(7000,7000+k)),[8000+r],[1,3]))
    ir.pm_nodes.extend(Node(r,'BW_div',[8000+r,9000+r],[8100+r],[scalar]) for r in range(k))
    vc=rel.certificates[0]
    vo=replace(vo,source=replace(vo.source,step_triple=('sm:1:0',*(f'pm:{p}:0' for p in vp))))
    vc=replace(vc,input_fact=vi.source,output_fact=vo.source,sm_step_id='sm:1:0',pm_step_ids=tuple(f'pm:{p}:0' for p in vp))
    ai=replace(vi,fact_id='fact_ai',sm_tid=700,pm_tids=tuple(range(7000,7000+k)),full_shape=(b,s*k,n,d*k),shard_shape=(b,s,n,d*k),source=rc.RelationFactSpec('sharded',('init:700',*(f'init:{u}' for u in range(7000,7000+k))),gather_dim=1))
    ao=replace(ai,fact_id='fact_ao',gather_dim=3,pm_tids=tuple(range(8000,8000+k)),shard_shape=(b,s*k,n,d),source=rc.RelationFactSpec('sharded',('init:700',*(f'pm:{p}:0' for p in ap)),gather_dim=3))
    do=replace(ao,fact_id='fact_do',sm_tid=701,pm_tids=tuple(range(8100,8100+k)),source=rc.RelationFactSpec('sharded',('sm:0:0',*(f'pm:{p}:0' for p in dp)),gather_dim=3))
    ac=rc.KRankAllToAllRelationCertificate(A_RULE,k,1,3,ai.source,ao.source,tuple(f'pm:{p}:0' for p in ap),A_THEOREM)
    dc=rc.KRankDivCertificate(D_RULE,k,3,scalar,ao.source,do.source,'sm:0:0',tuple(f'pm:{p}:0' for p in dp),do.full_shape,do.shard_shape,D_THEOREM)
    template=rel.transition_specs[0]
    rel.certificates=(vc,ac,dc)
    rel.transition_specs=tuple(replace(template,transition_id=f'transition_{j}',rule_id=c.rule_id,lean_theorem=c.lean_theorem,pre_facts=(c.input_fact,),post_facts=(c.output_fact,),sm_node_indices=sm,pm_node_indices=pm,certificate_digest=_typed_certificate_digest(c)) for j,(c,sm,pm) in enumerate(((vc,(1,),vp),(ac,(),ap),(dc,(0,),dp))))
    chain.relation_facts=(vi,vo,ai,ao,do)
    chain.states=(replace(chain.states[0],fact_ids=(vi.fact_id,ai.fact_id)),replace(chain.states[1],fact_ids=(vo.fact_id,do.fact_id)))
    chain.segments=(replace(chain.segments[0],transition_ids=tuple(t.transition_id for t in rel.transition_specs),sm_range=(0,2),pm_range=(0,3*k)),)
    ir.sm_graph_ref='FlattenAllToAllDiv.smGraph';ir.pm_graph_ref='FlattenAllToAllDiv.pmGraph';ir.pm_num_ranks=k
    return ir,rel




def witness_source(k=3):
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    from trainverify.bridge_emitter.bw_flatten_alltoall_div_renderer import render_closed_bw_flatten_alltoall_div_segment
    ir,rel=renderer_fixture(k)
    return fixture_source(ir,rel,render_closed_bw_flatten_alltoall_div_segment,pm_num_ranks=k).replace('SyntheticBWLayernorm','FlattenAllToAllDiv').replace('import denote.KRankBWLayernorm','import denote.KRankViewFlatten')
