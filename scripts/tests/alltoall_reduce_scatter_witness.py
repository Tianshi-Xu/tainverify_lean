"""Portable independent A2A/RS witnesses and read-only captured authority loader."""
from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace
import json
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.composer import _typed_certificate_digest
from trainverify.bridge_emitter.parser import Node

A_RULE = "alltoall-k-rank-layout-transport"
A_THEOREM = "TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn"
R_RULE = "reduce-scatter-reconstruction-k-rank"
R_THEOREM = "TrainVerify.Denote.allGatherPrimDimN_chunks_ofFn"




def renderer_fixture(k=3):
    full=(2,3*k,5*k);a_in=tuple(100+r for r in range(k));r_in=tuple(200+r for r in range(k))
    a_out=tuple(300+r for r in range(k));r_out=tuple(400+r for r in range(k))
    facts=[];certs=[];transitions=[]
    for name,kind,tid,inputs,outputs,dim,shape,positions in [('a','sharded',10,a_in,a_out,1,(2,3,5*k),tuple(range(0,2*k,2))),('r','reduction',20,r_in,r_out,None,full,tuple(range(1,2*k,2)))]:
        pre=rc.RelationFactSpec(kind,(f'init:{tid}',*(f'init:{t}' for t in inputs)),gather_dim=dim)
        post=rc.RelationFactSpec('sharded',(f'init:{tid}',*(f'pm:{p}:0' for p in positions)),gather_dim=2)
        for suffix,src,tids,piece in [('in',pre,inputs,shape),('out',post,outputs,(2,3*k,5))]:
            facts.append(rc.ClosedRelationFactRecord(name+'_'+suffix,src,src.layout,tid,tids,None,None,full,piece,gather_dim=src.gather_dim))
        steps=tuple(f'pm:{p}:0' for p in positions)
        c=rc.KRankAllToAllRelationCertificate(A_RULE,k,1,2,pre,post,steps,A_THEOREM) if name=='a' else rc.KRankReduceScatterReconstructionCertificate(R_RULE,k,2,full,(2,3*k,5),pre,post,steps,R_THEOREM)
        certs.append(c)
        transitions.append(rc.CertificateTransitionSpec(name,c.rule_id,(pre,),(post,),(),positions,c.lean_theorem,certificate_digest=_typed_certificate_digest(c)))
    nodes=[]
    for r in range(k):nodes.extend([Node(r,'AllToAllPrim',list(a_in),[a_out[r]],[1,2]),Node(r,'ReduceScatterPrim',list(r_in),[r_out[r]],[2])])
    states=(rc.ClosedRelationStateRecord('before',('a_in','r_in')),rc.ClosedRelationStateRecord('after',('a_out','r_out')))
    seg=rc.ClosedDependentSegmentRecord('segment_000000','component','before','after',('a','r'),(0,0),(0,2*k))
    chain=SimpleNamespace(complete=True,relation_facts=tuple(facts),authority_facts=(),anchor_fact=None,states=states,segments=(seg,))
    ir=SimpleNamespace(sm_nodes=[],pm_nodes=nodes,sm_num_ranks=1,pm_num_ranks=k,sm_graph_ref='AllToAllReduceScatter.smGraph',pm_graph_ref='AllToAllReduceScatter.pmGraph')
    return ir,SimpleNamespace(certificates=tuple(certs),transition_specs=tuple(transitions),dependent_chain_plan=chain)


def witness_source(k=3):
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    from trainverify.bridge_emitter.alltoall_reduce_scatter_renderer import render_closed_alltoall_reduce_scatter_segment
    ir,rel=renderer_fixture(k)
    return fixture_source(ir,rel,render_closed_alltoall_reduce_scatter_segment,pm_num_ranks=k).replace('SyntheticBWLayernorm','AllToAllReduceScatter').replace('import denote.KRankBWLayernorm','import denote.KRankAllToAll')
