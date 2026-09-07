"""Portable independent-input mixed atomic fixtures; no filesystem side effects."""
from types import SimpleNamespace as NS
from dataclasses import replace


def renderer_fixture(k=2, b=2, s=5, n=3, d=7, unflatten_count=1, linear_count=2, overlap_ids=False):
    from trainverify.bridge_emitter import relation_compiler as rc
    from trainverify.bridge_emitter.parser import Node
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    if min(k,b,s,n,d,unflatten_count,linear_count)<1:
        raise ValueError('positive dimensions/counts required')
    count=unflatten_count+linear_count
    sm=[]; pm=[]; records=[]; certs=[]; transitions=[]; pres=[]; posts=[]
    # Transition enumeration puts views first, SM executes linears first.
    sm_order=list(range(unflatten_count,count))+list(range(unflatten_count))
    pm_order=[(j,r) for r in range(k) for j in range(count)]
    sm_positions={j:i for i,j in enumerate(sm_order)}
    pm_positions={(j,r):i for i,(j,r) in enumerate(pm_order)}
    sm_nodes={};pm_nodes={}
    for j in range(count):
        base=10000*(j+1); si=sm_positions[j]; pis=tuple(pm_positions[j,r] for r in range(k))
        view=j<unflatten_count
        rule='fw-view-unflatten-sequence-sharded-k-rank' if view else 'linear-output-sharded-k-rank'
        theorem=rc.get_closed_rule_spec(rule).lean_theorems[0]
        x=rc.RelationFactSpec('sharded' if view else 'joined', (f'init:{base}',*(f'init:{base+100+r}' for r in range(k))) if view else (f'init:{base}',),gather_dim=1 if view else None,joined_pm_step=None if view else f'init:{base+100}')
        y=rc.RelationFactSpec('sharded',(f'sm:{si}:0',*(f'pm:{i}:0' for i in pis)),gather_dim=1 if view else 2)
        xf=(b,s*k,n*d) if view else (b,s,d); xs=(b,s,n*d) if view else xf
        yf=(b,s*k,n,d) if view else (b,s,n*k); ys=(b,s,n,d) if view else (b,s,n)
        xr=rc.ClosedRelationFactRecord(f'x{j}',x,x.layout,base,tuple(base+100+r for r in range(k)) if view else (),None,None,xf,xs,gather_dim=x.gather_dim,joined_pm_tid=None if view else base+100)
        yr=rc.ClosedRelationFactRecord(f'y{j}',y,'sharded',base+1,tuple(base+200+r for r in range(k)),None,None,yf,ys,gather_dim=y.gather_dim)
        records.extend((xr,yr));pres.append(xr.fact_id);posts.append(yr.fact_id)
        if view:
            c=rc.KRankBWViewFlattenCertificate(rule,k,x,y,f'sm:{si}:0',tuple(f'pm:{i}:0' for i in pis),theorem)
            ins=[base];pins=[[base+100+r] for r in range(k)]
            pre=(x,)
        else:
            w=rc.RelationFactSpec('sharded',(f'init:{base+2}',*(f'init:{base+300+r}' for r in range(k))),gather_dim=0)
            wr=rc.ClosedRelationFactRecord(f'w{j}',w,'sharded',base+2,tuple(base+300+r for r in range(k)),None,None,(n*k,d),(n,d),gather_dim=0)
            records.append(wr);pres.append(wr.fact_id)
            c=rc.KRankOutputShardedLinearCertificate(rule,k,2,x,w,y,f'sm:{si}:0',tuple(f'pm:{i}:0' for i in pis),xf,(n*k,d),(n,d),yf,ys,theorem)
            ins=[base,base+2];pins=[[base+100,base+300+r] for r in range(k)];pre=tuple(sorted((x,w)))
        certs.append(c)
        transitions.append(rc.CertificateTransitionSpec(f't{j}',rule,pre,(y,),(si,),pis,theorem,certificate_digest=_typed_certificate_digest(c)))
        sm_nodes[j]=Node(0,'FW_view' if view else 'FW_linear',ins,[base+1],list(yf) if view else [])
        for r in range(k):pm_nodes[j,r]=Node(r,'FW_view' if view else 'FW_linear',pins[r],[base+200+r],list(ys) if view else [])
    sm=[sm_nodes[j] for j in sm_order];pm=[pm_nodes[j,r] for j,r in pm_order]
    if overlap_ids:
        view=certs[0];linear=certs[unflatten_count]
        tid=next(r for r in records if r.source==linear.output_fact).pm_tids[0]
        sm[sm_positions[0]].outs=[tid]
        records=[replace(r,sm_tid=tid) if r.source==view.output_fact else r for r in records]
    anchor=rc.ClosedTensorShapeFactRecord('anchor','sm',999,(1,),999)
    auth=(rc.ClosedTensorShapeFactRecord('protected_pm','pm',998,(1,),998),)
    before=rc.ClosedRelationStateRecord('state_before',('anchor','protected_pm',*pres))
    after=rc.ClosedRelationStateRecord('state_after',(*before.fact_ids,*posts))
    seg=rc.ClosedDependentSegmentRecord('segment_000000','component',before.state_id,after.state_id,tuple(t.transition_id for t in transitions),(0,len(sm)),(0,len(pm)))
    chain=NS(complete=True,relation_facts=tuple(records),authority_facts=auth,anchor_fact=anchor,states=(before,after),segments=(seg,))
    return NS(sm_nodes=sm,pm_nodes=pm,sm_num_ranks=1,pm_num_ranks=k,sm_graph_ref='MixedGraph.sm',pm_graph_ref='MixedGraph.pm'),NS(dependent_chain_plan=chain,certificates=tuple(certs),transition_specs=tuple(transitions)),seg.segment_id


def witness_source(k=2,b=2,s=5,n=3,d=7,unflatten_count=1,linear_count=2,overlap_ids=False):
    from trainverify.bridge_emitter.composer import _node_text,render_closed_relation_declarations
    from trainverify.bridge_emitter.unflatten_output_linear_renderer import render_closed_unflatten_output_linear_segment
    ir,rel,sid=renderer_fixture(k,b,s,n,d,unflatten_count,linear_count,overlap_ids)
    namespace=f'UnflattenOutputK{k}N{unflatten_count}M{linear_count}'
    graph=namespace+'Graph';ir.sm_graph_ref=graph+'.sm';ir.pm_graph_ref=graph+'.pm'
    decl=render_closed_relation_declarations(rel.dependent_chain_plan,namespace)
    suffix=f'end\nend TrainVerify.Denote.{namespace}\n'
    assert decl.endswith(suffix)
    imports=[line for line in decl.splitlines() if line.startswith('import ')]
    body='\n'.join(line for line in decl[:-len(suffix)].splitlines() if not line.startswith('import '))
    return '\n'.join([*imports,'import denote.KRankViewUnflatten','import denote.KRankLinearGather','set_option maxHeartbeats 500000','open TrainVerify.Denote',f'namespace {graph}','def sm : GraphDecl := { numRanks := 1, nodes := ['+', '.join(map(_node_text,ir.sm_nodes))+'] }',f'def pm : GraphDecl := {{ numRanks := {k}, nodes := ['+', '.join(map(_node_text,ir.pm_nodes))+'] }',f'end {graph}',body,render_closed_unflatten_output_linear_segment(ir,rel,sid),f'#print axioms {sid}',suffix])
