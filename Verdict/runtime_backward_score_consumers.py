"""Original score-gradient DAG: matmul -> softmax -> AA -> div -> AA -> matmul.

Every exchange and ordered peer is retained. Shared value definitions avoid
copying expanded ancestor expressions into each target. This is same-Store
composition, not a new cross-model equivalence or successful-run assertion.
"""
from copy import copy
from Verdict.runtime_lineage import _same_typed
from Verdict import graph_to_lean as compiler
from Verdict import runtime_backward_softmax_consumers as initial_softmax
from Verdict import runtime_backward_softmax_reads as softmax
from Verdict import runtime_backward_matmul_reads as matmul
from Verdict import runtime_backward_collective_reads as collective


def _consumer(cells, ref, rank, op):
    rows=[(i,c) for i,c in enumerate(cells) if c.rank==rank and any(
        _same_typed(tuple(r),tuple(ref)) for r in c.inputs)]
    if len(rows)!=1 or rows[0][1].opname.name!=op:
        raise ValueError('score-backward unique original local '+op+' consumer required')
    return rows[0][0]


def render(worlds,capture_path,rank_code_directory):
    from Verdict import runtime_backward_div_reads as division
    _,base=initial_softmax.render(worlds)
    definitions=[];dag=[];by_ref={};div_reads=[];coll_reads=[];mat_reads=[];targets=[]
    sources={'div':[],'collective':[],'matmul':[]}

    def register(label,index,tid,ref,expression,steps,projection=None,source_node=None):
        key=(label,tuple(ref))
        if key in by_ref:
            raise ValueError('score-backward duplicate original output authority')
        suffix='' if projection is None else '_'+str(projection)
        value=f'backwardScoreValue_{label}_{index}{suffix}'
        name=f'backwardScoreRead_{label}_{index}{suffix}'
        definitions.extend([f'def {value} (t : Store) : Tensor := {expression}',
            f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
            f'    t {tid} = {value} t := by',f'  change t {tid} = {expression}',
            *['  '+x for x in steps],f'#print axioms {name}'])
        row=dict(world=label,source_index=index,output_tid=tid,output_ref=ref,
                 value_name=value,theorem=name,expression=expression,projection=projection,source_node=source_node)
        dag.append(row);by_ref[key]=row
        return row

    def prior(label,ref):
        row=by_ref.get((label,tuple(ref)))
        if row is None:
            raise ValueError('score-backward missing certified original operand edge')
        return row

    for view,cells,snapshot,order,label in worlds:
        if label=='pm':
            snapshot=compiler._load_chunk_source(capture_path,rank_code_directory)
            checked=copy(view);compiler.attach_collective_scopes(checked,snapshot);view=checked
        roots={}
        for b in base['reads']:
            if b['world']!=label: continue
            r=b['softmax'];rank=cells[r['source_index']].rank
            roots[rank]=register(label,r['source_index'],r['output_tid'],r['output_ref'],b['expression'],
                                 ['exact '+b['theorem']+' s t h'])

        def exchange(heads,reader):
            result={}
            for rank,p in heads.items():
                i=_consumer(cells,p['output_ref'],rank,'AllToAllPrim')
                text,r=collective.render_read(view,cells,snapshot,i,order,label,reader,0)
                parents=[prior(label,ref) for ref in r['input_refs']]
                idim,odim=r['params']
                expr=f'AllToAllSourceFaithful.tensor {len(r["ranks"])} {r["local_index"]} {idim} {odim} ['+', '.join(p['value_name']+' t' for p in parents)+']'
                steps=['rw ['+r['theorems'][0]+' s t h]', 'simp only [List.map_cons,List.map_nil]',
                       'rw ['+', '.join(p['theorem']+' s t h' for p in parents)+']']
                result[rank]=register(label,i,r['output_tid'],r['output_ref'],expr,steps)
                coll_reads.append(r);sources['collective'].append(text)
            return result

        if label=='pm': roots=exchange(roots,softmax.render_read)
        div_heads={}
        for rank,p in roots.items():
            i=_consumer(cells,p['output_ref'],rank,'BW_div')
            text,r=division.render_read(view,cells,snapshot,i,order,label)
            if not _same_typed(r['input_refs'][0],p['output_ref']) or r['input_tids'][0]!=p['output_tid']:
                raise ValueError('score-backward original div cotangent join mismatch')
            divisor,=r['params']
            expr=f'bw_div ({divisor} : Scalar) ({p["value_name"]} t)'
            div_heads[rank]=register(label,i,r['output_tid'],r['output_ref'],expr,
                ['rw ['+r['theorems'][0]+' s t h, '+p['theorem']+' s t h]'])
            div_reads.append(r);sources['div'].append(text)
        roots=exchange(div_heads,division.render_read) if label=='pm' else div_heads
        for rank,p in roots.items():
            i=_consumer(cells,p['output_ref'],rank,'BW_matmul')
            text,r=matmul.render_read(view,cells,snapshot,i,order,label)
            if not _same_typed(r['input_refs'][0],p['output_ref']) or r['input_tids'][0]!=p['output_tid']:
                raise ValueError('score-backward original matmul cotangent join mismatch')
            for port in (0,1):
                expr=f'(bw_matmul ({p["value_name"]} t) (t {r["input_tids"][1]}) (t {r["input_tids"][2]})).{port+1}'
                target=register(label,i,r['output_tids'][port],r['output_refs'][port],expr,
                    ['rw ['+r['theorems'][port]+' s t h, '+p['theorem']+' s t h]'],port+1,r)
                targets.append(target)
            mat_reads.append(r);sources['matmul'].append(text)
    return '\n'.join(definitions)+'\n',dict(dag=dag,targets=targets,div_reads=div_reads,
        collective_reads=coll_reads,matmul_reads=mat_reads,sources={k:''.join(v) for k,v in sources.items()},
        proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False)
