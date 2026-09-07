"""Portable candidates and exact retained-inventory replay; Python only."""
from dataclasses import replace
from types import SimpleNamespace
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.composer import _typed_certificate_digest
from trainverify.bridge_emitter.parser import Node




def renderer_fixture(k=3):
    from scripts.tests.bw_linear_dw_row_witness import renderer_fixture as row
    ir,rel=row(k,with_dx=True)
    chain=rel.dependent_chain_plan
    # Opposite SM/PM authority order, exactly as in the captured atomic SCC.
    ir.sm_nodes.insert(0,Node(0,'BW_matmul',[600,700,800],[900,901],[]))
    ir.pm_nodes.extend(Node(r,'BW_matmul',[6000+r,7000+r,8000+r],[9000+r,10000+r],[]) for r in range(k))
    records=[]; mapping={}
    for r in chain.relation_facts:
        source=r.source
        if source.step_triple[0].startswith('sm:0:'):
            source=replace(source,step_triple=(source.step_triple[0].replace('sm:0:','sm:1:'),*source.step_triple[1:]))
        mapping[r.source]=source; records.append(replace(r,source=source))
    certs=[];trans=[]
    for c,t in zip(rel.certificates,rel.transition_specs):
        c=replace(c,output_fact=mapping[c.output_fact],sm_step_id=c.sm_step_id.replace('sm:0:','sm:1:'))
        certs.append(c);trans.append(replace(t,post_facts=(c.output_fact,),sm_node_indices=(1,),certificate_digest=_typed_certificate_digest(c)))
    def fact(name,sm,pm,shape,slot=None):
        full=(shape[0],shape[1]*k,*shape[2:])
        source=rc.RelationFactSpec('sharded',(f'init:{sm}',*(f'init:{v}' for v in pm)),gather_dim=1) if slot is None else rc.RelationFactSpec('sharded',(f'sm:0:{slot}',*(f'pm:{k+r}:{slot}' for r in range(k))),gather_dim=1)
        rec=rc.ClosedRelationFactRecord(name,source,'sharded',sm,tuple(pm),None,None,full,shape,gather_dim=1)
        records.append(rec);return source
    g=fact('mg',600,range(6000,6000+k),(2,2,3,7))
    x=fact('mx',700,range(7000,7000+k),(2,2,3,5))
    y=fact('my',800,range(8000,8000+k),(2,2,5,7))
    for slot,shape,sm,base in ((0,(2,2,3,5),900,9000),(1,(2,2,5,7),901,10000)):
        out=fact(f'mo{slot}',sm,range(base,base+k),shape,slot)
        c=rc.KRankBWMatmulCertificate(rule_id='bw-matmul-head-sharded-k-rank',family='head-sharded',projection=f'.{slot+1}',rank_count=k,input_facts=(g,x,y),output_fact=out,sm_step_id=f'sm:0:{slot}',pm_step_ids=tuple(f'pm:{k+r}:{slot}' for r in range(k)),lean_theorem=f'TrainVerify.Denote.bw_matmul_{"fst" if slot==0 else "snd"}_head_gather_rank4')
        certs.append(c);trans.append(rc.CertificateTransitionSpec(f'mat{slot}',c.rule_id,tuple(sorted(c.input_facts)),(out,),(0,),tuple(range(k,2*k)),c.lean_theorem,certificate_digest=_typed_certificate_digest(c)))
    chain.relation_facts=tuple(records)
    chain.states=tuple(replace(s,fact_ids=(*s.fact_ids,'mg','mx','my',*(('mo0','mo1') if j else ()))) for j,s in enumerate(chain.states))
    chain.segments=(replace(chain.segments[0],transition_ids=tuple(t.transition_id for t in trans),sm_range=(0,2),pm_range=(0,2*k)),)
    rel.certificates=tuple(certs);rel.transition_specs=tuple(trans)
    ir.sm_graph_ref='SyntheticRowHead.smGraph';ir.pm_graph_ref='SyntheticRowHead.pmGraph'
    return ir,rel


def witness_source(k=3):
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    from trainverify.bridge_emitter.bw_row_linear_head_matmul_renderer import render_closed_bw_row_linear_head_matmul_segment
    ir,rel=renderer_fixture(k)
    return fixture_source(ir,rel,render_closed_bw_row_linear_head_matmul_segment,pm_num_ranks=k).replace('SyntheticBWLayernorm','SyntheticRowHead').replace('import denote.KRankBWLayernorm','import denote.KRankBWLinearDwRowGeneral\nimport denote.KRankBWLinearDxRow\nimport denote.KRankBWMatmulHead')
