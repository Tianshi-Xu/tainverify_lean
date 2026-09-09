"""Source-authenticated embedding producer reads on original final Stores.

Called after initial relation binding has retraced the original source lineages.
Operand nonwrites are checked here and independently in generated Lean.
"""
from Verdict.runtime_lineage import Role


def render(sm, pm, lineages, order):
    text=[]; reads=[]; seen=set()
    for lineage in lineages:
        if lineage.role != Role.ACTIVATION:
            continue
        endpoints=[('sm',sm,lineage.target)]+[
            ('pm',pm,p.endpoint) for u in lineage.units for p in u.pieces]
        for label,view,e in endpoints:
            if e.ref in seen:continue
            nodes=view.nodes()
            matches=[i for i,n in enumerate(nodes) if tuple(n)==e.writer]
            if len(matches)!=1:raise ValueError('embedding original writer not unique')
            index=matches[0];n=nodes[index]
            if str(view.node_opname(n)).split('.')[-1]!='FW_embedding':continue
            ins=[t.tid for t in view.node_inputs(n)];outs=[t.tid for t in view.node_outputs(n)]
            if len(ins)!=2 or outs!=[e.tid]:raise ValueError('embedding original ports mismatch')
            ids,weight=ins;k=order[label]['execution_to_source'].index(index)
            for i in order[label]['execution_to_source'][k:]:
                if set(ins)&{t.tid for t in view.node_outputs(nodes[i])}:
                    raise ValueError('embedding operand is written by node or suffix')
            node=f'{label}Node_{index}';requests=f'{label}InputRequests';name=f'embeddingRead_{e.tid}'
            text += [f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
                f'    t {e.tid} = fw_embedding (t {ids}) (t {weight}) := by',
                f'  apply SourceEmbeddingRead.embedding_value_of_split {label}Graph {label}Scope {label}Peers {label}Graph.nodes',
                f'    {requests} ({requests}.take {k}) ({requests}.drop {k+1}) {node} {n.rank} {ids} {weight} {e.tid} s t rfl ?_ rfl ?_ ?_ h',
                '  · calc',
                f'      {requests} = {requests}.take {k} ++ {requests}.drop {k} := (List.take_append_drop {k} {requests}).symm',
                '      _ = _ := rfl',
                f'  · change ∀ row ∈ {requests}.drop {k}, {ids} ∉ row.1.outs',
                '    decide',
                f'  · change ∀ row ∈ {requests}.drop {k}, {weight} ∉ row.1.outs',
                '    decide',f'#print axioms {name}']
            seen.add(e.ref)
            reads.append(dict(theorem=name,world=label,ref=list(e.ref),source_index=index,execution_index=k,
                              input_tids=ins,output_tid=e.tid))
    source='\n'.join(['namespace TrainVerify.Denote.RuntimeWorld','noncomputable section',
        'set_option maxHeartbeats 500000',*text,'end','end TrainVerify.Denote.RuntimeWorld',''])
    return source,dict(reads=reads,proof_admissible=False,kernel_value_proved=False,torch_refinement=False)
