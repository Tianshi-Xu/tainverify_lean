"""Backward shape queries on the existing complete shared prefix proof DAG.

The prefix inventory selects existing theorem names, never proves their claims.
The caller imports the exact original Data/prefix modules and must kernel-check
these projections. Initial parameter shapes are premises; final shapes are not.
No new prefix, altered evaluator, canonical entry or value relation is created.
"""
import re
from Verdict.runtime_lineage import _same_typed
from Verdict.runtime_backward_linear_reads import render_read


def render(worlds,indices,prefix,*,seed_config=None):
    view,cells,snapshot,order,label=worlds[1];sequence=order['execution_to_source'];n=len(sequence)
    if label!='pm' or not indices or any(type(i) is not int or not 0<=i<len(cells) for i in indices) or len(indices)!=len(set(indices)):
        raise ValueError('bw-prefix unique original PM linear projection required')
    if (prefix.get('status')!='conditional-prefix-emitted' or prefix.get('frontier') is not None
            or not _same_typed(prefix.get('prefix_length'),n)
            or not _same_typed(prefix.get('prefix_nodes'),sequence)):
        raise ValueError('bw-prefix complete original execution coverage required')
    stem='pmSeededPrefix';names=prefix['kernel_checks']
    if len(names)!=len(set(names)) or any(type(x) is not str for x in names):
        raise ValueError('bw-prefix unique shared declaration inventory required')
    names=set(names);endpoints={}
    for name in names:
        m=re.fullmatch(stem+r'NoWrite_(\d+)_(\d+)',name)
        if m:
            a,b=map(int,m.groups())
            if not 0<=a<b<=n:raise ValueError('bw-prefix invalid frame interval')
            endpoints.setdefault(b,[]).append(a)
    required={f'{stem}Run_0_{n}'}
    if not required<=names:raise ValueError('bw-prefix complete shared run certificate required')
    proof=[f'theorem backwardPrefixRun_pm (s : Store) (hi : {stem}InitShapes s) :',
        f'    pmSeededDenoteWithInputs s = some ({stem}State_{n} s) := by',
        '  unfold pmSeededDenoteWithInputs', '  rw [pmDenoteWithInputs_entry]',
        f'  have hp : SourceScopedEval.runUsing (fun row a => SourceScopedEval.stepWithInputs pmGraph',
        f'      (pmScope row.1) (pmPeers row.1) a row.1 row.2) (pmInputRequests.take {n})',
        f'      (some (pmInitialWithSeeds s)) = some ({stem}State_{n} s) := by',
        f'    rw [{stem}RequestsCoverage]',f'    exact {stem}Run_0_{n} s hi',
        f'  have ht : pmInputRequests.take {n} = pmInputRequests := by rfl',
        '  rw [ht] at hp','  exact hp','#print axioms backwardPrefixRun_pm',
        f'theorem backwardPrefixFinal_pm (s t : Store) (hi : {stem}InitShapes s)',
        '    (hrun : pmSeededDenoteWithInputs s = some t) :',f'    t = {stem}State_{n} s :=',
        '  Option.some.inj (hrun.symm.trans (backwardPrefixRun_pm s hi))',
        '#print axioms backwardPrefixFinal_pm']
    rows=[];nodes=view.nodes();queries=[]
    for index in indices:
        render_read(view,cells,snapshot,index,order,label)
        node=nodes[index]
        queries.extend((index,role,tensor) for role,tensor in
            [('cotangent',view.node_inputs(node)[0]),('saved_primal',view.node_inputs(node)[1]),('dx',view.node_outputs(node)[0])])
    if seed_config is not None:
        from Verdict.runtime_backward_seed_reads import render as seed_render
        _,authenticated=seed_render(worlds,seed_config,seed_config['pm_run'])
        for row in authenticated['reads']:
            if row['world']!='pm':continue
            i=row['source_index']
            queries.append((i,'seed_primal',view.node_inputs(nodes[i])[1]))
    for index,role,tensor in queries:
        matches=[(j,p) for j,i in enumerate(sequence) for p,t in enumerate(view.node_outputs(nodes[i])) if t.tid==tensor.tid]
        if len(matches)!=1:raise ValueError('bw-prefix unique original versioned writer required')
        j,port=matches[0];shape=list(view.tensor_shape(tensor));tid=tensor.tid
        dependencies=[f'{stem}Written_{j}_{port}',f'{stem}Shape_{j}_{port}']
        if not set(dependencies)<=names:raise ValueError('bw-prefix shared writer/shape certificate missing')
        frames=[];end=n
        while end>j+1:
            start=min([a for a in endpoints.get(end,[]) if a>=j+1]+[end-1])
            name=f'{stem}Skip_{start}' if end==start+1 else f'{stem}NoWrite_{start}_{end}'
            if name not in names:raise ValueError('bw-prefix full suffix frame certificate missing')
            if any(tid in [t.tid for t in view.node_outputs(nodes[k])] for k in sequence[start:end]):
                raise ValueError('bw-prefix original tensor overwritten in full execution suffix')
            frames.append([start,end]);dependencies.append(name);end=start
        name=f'backwardPrefixShape_pm_{index}_{role}'
        proof += [f'theorem {name} (s t : Store) (hi : {stem}InitShapes s)',
            f'    (hrun : pmSeededDenoteWithInputs s = some t) : (t {tid}).shape = {shape} := by',
            '  rw [backwardPrefixFinal_pm s t hi hrun]']
        for (a,b),frame in zip(frames,dependencies[2:],strict=True):
            proof.append(f'  rw [{frame} s {tid} (by decide)]')
        proof += [f'  rw [{dependencies[0]} s]',f'  exact {dependencies[1]} s hi',f'#print axioms {name}']
        rows.append(dict(source_index=index,role=role,tid=tid,ref=list(view.source_tensor(tensor)),shape=shape,
            writer_source_index=sequence[j],writer_execution_index=j,writer_port=port,frames=frames,dependencies=dependencies,theorem=name))
    return '\n'.join(proof)+'\n',dict(reads=rows,proof_admissible=False,kernel_value_proved=False,
        public_complete=False,torch_refinement=False)
