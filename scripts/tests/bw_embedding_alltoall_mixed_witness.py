"""Portable mixed embedding fixtures and read-only frozen production replay."""
from types import SimpleNamespace
from dataclasses import replace


def renderer_fixture(k=3,b=2,s=5,v=13,d=7):
    from trainverify.bridge_emitter import relation_compiler as rc
    from trainverify.bridge_emitter.parser import Node
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    if any(type(x) is not int or x<=0 for x in (k,b,s,v,d)):raise ValueError('positive dimensions required')
    # Prior chunk writers remain outside the atomic frame, like actual ordinal 186.
    chunks=tuple(100+r for r in range(k));g=tuple(100+k+r for r in range(k));ag=tuple(100+2*k+r for r in range(k));w=tuple(100+3*k+r for r in range(k));ho=tuple(100+4*k+r for r in range(k));ao=tuple(100+5*k+r for r in range(k));qo=tuple(100+6*k+r for r in range(k))
    pm=[Node(r,'ChunkPrim',[6],[chunks[r]],[1]) for r in range(k)]
    hp=[];ap=[];qp=[]
    for r in range(k-1):hp.append(len(pm));pm.append(Node(r,'BW_embedding',[g[r],2,w[r]],[ho[r]],[]))
    for r in range(k):ap.append(len(pm));pm.append(Node(r,'AllToAllPrim',list(ag),[ao[r]],[2,1]))
    hp.append(len(pm));pm.append(Node(k-1,'BW_embedding',[g[-1],2,w[-1]],[ho[-1]],[]))
    for r in range(k):qp.append(len(pm));pm.append(Node(r,'BW_embedding',[ao[r],chunks[r],7],[qo[r]],[]))
    sm=[Node(0,'BW_embedding',[5,6,7],[8],[]),Node(0,'BW_embedding',[1,2,3],[4],[])]
    records=[]
    def fact(name,kind,axis,ts,tps,full,shard,refs=None):
        f=rc.RelationFactSpec(kind,refs or (f'init:{ts}',*(f'init:{t}' for t in tps)),gather_dim=axis)
        records.append(rc.ClosedRelationFactRecord(name,f,kind,ts,tuple(tps),None,None,full,shard,gather_dim=axis));return f
    hg=fact('hg','sharded',2,1,g,(b,s*k,d*k),(b,s*k,d))
    hi=fact('hi','sharded',0,2,(2,),(b,s*k),(b,s*k))
    hw=fact('hw','sharded',1,3,w,(v,d*k),(v,d))
    ai=fact('ai','sharded',2,5,ag,(b,s*k,d*k),(b,s*k,d))
    qi=fact('qi','chunked',1,6,chunks,(b,s*k),(b,s),(f'init:6',*(f'pm:{i}:0' for i in range(k))))
    qw=fact('qw','sharded',0,7,(7,),(v+1,d*k),(v+1,d*k))
    hpost=fact('ho','sharded',1,4,ho,(v,d*k),(v,d),('sm:1:0',*(f'pm:{i}:0' for i in hp)))
    apost=fact('ao','sharded',1,5,ao,(b,s*k,d*k),(b,s,d*k),('init:5',*(f'pm:{i}:0' for i in ap)))
    qpost=fact('qo','reduction',None,8,qo,(v+1,d*k),(v+1,d*k),('sm:0:0',*(f'pm:{i}:0' for i in qp)))
    hs=rc.get_closed_rule_spec('bw-embedding-hidden-sharded-k-rank');aas=rc.get_closed_rule_spec('alltoall-k-rank-layout-transport');qs=rc.get_closed_rule_spec('bw-embedding-sequence-reduction-k-rank')
    hc=rc.KRankBWEmbeddingHiddenCertificate(hs.rule_id,k,b,s*k,v,d,hg,hi,hw,hpost,'sm:1:0',tuple(f'pm:{i}:0' for i in hp),hs.lean_theorems[0])
    ac=rc.KRankAllToAllRelationCertificate(aas.rule_id,k,2,1,ai,apost,tuple(f'pm:{i}:0' for i in ap),aas.lean_theorems[0])
    qc=rc.KRankBWEmbeddingSequenceReductionCertificate(qs.rule_id,k,1,b,s,d*k,v+1,apost,rc.RelationFactSpec('sharded',('init:6','init:6'),gather_dim=0),qi,qw,qpost,'sm:0:0',tuple(f'pm:{i}:0' for i in range(k)),tuple(f'pm:{i}:0' for i in qp),qs.lean_theorems[0])
    certs=(hc,ac,qc)
    ts=tuple(rc.CertificateTransitionSpec(f't{i}',c.rule_id,tuple(sorted(ins)),(out,),si,tuple(pi),c.lean_theorem,certificate_digest=_typed_certificate_digest(c)) for i,(c,ins,out,si,pi) in enumerate(((hc,(hg,hi,hw),hpost,(1,),hp),(ac,(ai,),apost,(),ap),(qc,(apost,qi,qw),qpost,(0,),qp))))
    before=rc.ClosedRelationStateRecord('state_before',('anchor','hg','hi','hw','ai','qi','qw'))
    after=rc.ClosedRelationStateRecord('state_after',(*before.fact_ids,'ho','qo'))
    seg=rc.ClosedDependentSegmentRecord('segment_000000','component',before.state_id,after.state_id,tuple(t.transition_id for t in ts),(0,2),(k,len(pm)))
    chain=SimpleNamespace(complete=True,relation_facts=tuple(records),authority_facts=(),anchor_fact=rc.ClosedTensorShapeFactRecord('anchor','sm',2,(b,s*k),2),states=(before,after),segments=(seg,))
    ir=SimpleNamespace(sm_num_ranks=1,pm_num_ranks=k,sm_nodes=sm,pm_nodes=pm,sm_graph_ref='Fixture.sm',pm_graph_ref='Fixture.pm')
    return ir,SimpleNamespace(dependent_chain_plan=chain,certificates=certs,transition_specs=ts),seg.segment_id


def witness_source(k=3,b=2,s=5,v=13,d=7):
    from trainverify.bridge_emitter.composer import _node_text,render_closed_relation_declarations
    from trainverify.bridge_emitter.bw_embedding_alltoall_mixed_renderer import render_closed_bw_embedding_alltoall_mixed_segment
    ir,rel,sid=renderer_fixture(k,b,s,v,d)
    ns=f'BWEmbeddingMixedK{k}B{b}S{s}V{v}D{d}'
    ir.sm_graph_ref=f'{ns}Graph.sm';ir.pm_graph_ref=f'{ns}Graph.pm'
    imports=['import denote.GraphGears','import denote.BWEmbeddingHiddenShardK','import denote.BWEmbeddingSequenceShardK','import denote.RelationCompiler']
    out=imports+['open TrainVerify.Denote',f'namespace {ns}Graph','def sm : GraphDecl := { numRanks := 1, nodes := ['+', '.join(_node_text(n) for n in ir.sm_nodes)+'] }',f'def pm : GraphDecl := {{ numRanks := {k}, nodes := ['+', '.join(_node_text(n) for n in ir.pm_nodes)+'] }',f'end {ns}Graph']
    declarations=render_closed_relation_declarations(rel.dependent_chain_plan,ns)
    suffix=f'end\nend TrainVerify.Denote.{ns}\n'
    assert declarations.endswith(suffix)
    out+=['\n'.join(l for l in declarations[:-len(suffix)].splitlines() if not l.startswith('import ')),render_closed_bw_embedding_alltoall_mixed_segment(ir,rel,sid),f'#print axioms {sid}_sound',suffix]
    return '\n'.join(out)
