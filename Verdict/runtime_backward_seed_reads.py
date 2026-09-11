"""Fresh authenticated scalar seed -> original BW_sum in the same final Store.

The existing seed loader authenticates capture/runtime observations. No caller
seed dictionary is trusted and no default scale is introduced here. These
fragments extend the shared DAG; they do not publish or modify its entry point.
"""
from Verdict import runtime_seed_feed as seeds, runtime_schedule, graph_to_lean
from Verdict.runtime_backward_linear_reads import _writer
from Verdict.runtime_lineage import _same_typed
from trainverify.backward_linear_authority import _ir_identity


def _read(view,cells,snapshot,order,label,seed,slot):
    from nnscaler.ir.operator import IRBpOperation
    nodes=view.nodes()
    if not _same_typed([tuple(n) for n in nodes],[tuple(c.node) for c in cells]):
        raise ValueError('bw-sum original ordered source inventory mismatch')
    indices=[i for i,c in enumerate(cells) if _same_typed(list(c.node),seed['consumer'])]
    if len(indices)!=1: raise ValueError('bw-sum original seed consumer missing/ambiguous')
    i,=indices;cell=cells[i];node=nodes[i]
    if (not isinstance(cell.ir,IRBpOperation) or cell.opname.name!='BW_sum'
            or cell.ir.mirror.signature!='torch.sum'):
        raise ValueError('bw-sum original typed operation/function mismatch')
    pairs=[(j,c) for j,c in enumerate(cells) if c.ir is cell.ir.mirror
           and (c.rank,c.mb,c.node.wtype)==(cell.rank,cell.mb,cell.node.wtype)]
    if len(pairs)!=1 or pairs[0][0]>=i: raise ValueError('bw-sum original forward mirror missing/ambiguous')
    fi,fw=pairs[0]
    if not _same_typed([tuple(r) for r in cell.inputs[1:]],[tuple(r) for r in fw.inputs]):
        raise ValueError('bw-sum original saved primal version/order mismatch')
    for c,name in ((fw,cell.ir.mirror.name),(cell,'BW.'+cell.ir.mirror.name)):
        if (not _same_typed(tuple(c.node),(c.wtype.value,c.rank,c.mb,c.ir.cid,name))
                or str(view.node_opname(c.node)).split('.')[-1]!=c.opname.name
                or not _same_typed(view.node_kwargs(c.node),c.kwargs)
                or set(c.kwargs)-{'__consts'} or c.kwargs.get('__consts',[])!=[]):
            raise ValueError('bw-sum original node/op/kwargs mismatch')
        params=graph_to_lean._get_node_params(view,c.node,num_parts=0)
        if params is not None and not _same_typed(params,[]):
            raise ValueError('bw-sum original empty params required')
        if any(c.node in getattr(view,key,{}) for key in ('collective_scopes','chunk_scopes','wred_scopes')):
            raise ValueError('bw-sum ordinary global scope required')
        for side,irs in [('inputs',c._input_irs),('outputs',c._output_irs)]:
            actual=getattr(view,'node_'+side)(c.node)
            if not _same_typed([tuple(view.source_tensor(t)) for t in actual],[tuple(r) for r in getattr(c,side)]):
                raise ValueError('bw-sum original lowered fullref/order mismatch')
            if not _same_typed([tuple(view.tensor_shape(t)) for t in actual],[tuple(ir.shape) for ir in irs]):
                raise ValueError('bw-sum original lowered shape mismatch')
    originals=list(cell.ir.inputs())+list(cell.ir.mirror.inputs())
    if len(originals)!=2 or len(cell.ir.outputs())!=1 or len(cell._input_irs)!=2 or len(cell.outputs)!=1:
        raise ValueError('bw-sum full-reduction arity mismatch')
    for actual,expected in ((cell._input_irs,originals),(cell._output_irs,list(cell.ir.outputs())),
                            (cell._input_irs[:1],[cell.ir.mirror.output(0).grad]),
                            (cell._output_irs,[cell.ir.mirror.input(0).grad])):
        if not _same_typed([_ir_identity(t) for t in actual],[_ir_identity(t) for t in expected]):
            raise ValueError('bw-sum saved/gradient IR identity mismatch')
    g,x=[t.tid for t in view.node_inputs(node)];out,=[t.tid for t in view.node_outputs(node)]
    if not _same_typed(seed['ref'],dict(zip(seeds.FIELDS,cell.inputs[0],strict=True))):
        raise ValueError('bw-sum authenticated seed fullref identity mismatch')
    if (not _same_typed(seed['tid'],g) or not _same_typed(seed['shape'],[1])
            or not _same_typed(seed['value'],1)):
        raise ValueError('bw-sum unsupported authenticated seed adapter contract')
    runtime_schedule.validate(view,order['execution_to_source'])
    sequence=order['execution_to_source'];k=sequence.index(i)
    for j in sequence[k:]:
        if {g,x}&{t.tid for t in view.node_outputs(nodes[j])}:
            raise ValueError('bw-sum operand written by selected node or full execution suffix')
    if any(g in [t.tid for t in view.node_outputs(n)] for n in nodes):
        raise ValueError('bw-sum external seed written in original graph')
    bw_writer=_writer(snapshot,cells,i);fw_writer=_writer(snapshot,cells,fi)
    request=f'{label}InputRequests'; stem=f'backwardSeed_{label}_{i}'
    proof=[f'theorem {stem}_read (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
        f'    t {out} = bw_sum (t {g}) (t {x}) := by',
        f'  apply SourceBWSumRead.bw_sum_value_of_split {label}Graph {label}Scope {label}Peers {label}Graph.nodes',
        f'    {request} ({request}.take {k}) ({request}.drop {k+1}) {label}Node_{i}',
        f'    {node.rank} {g} {x} {out} s t rfl ?_ rfl ?_ ?_ h',
        '  · calc',f'      {request} = {request}.take {k} ++ {request}.drop {k} := (List.take_append_drop {k} {request}).symm',
        '      _ = _ := rfl']
    for tid in (g,x): proof += [f'  · change ∀ row ∈ {request}.drop {k}, {tid} ∉ row.1.outs','    decide']
    proof += [f'#print axioms {stem}_read',
        f'theorem {stem}_seed (s t : Store) (h : {label}SeededDenoteWithInputs s = some t) :',
        f'    t {g} = unitSeed := by',
        f'  have hf := SourceParameterFrame.runWithInputs_frame {label}Graph {label}Scope {label}Peers',
        f'    {label}Graph.nodes {request} ({label}InitialWithSeeds s) t {g} (by decide) h',
        f'  exact hf.trans ({label}InitialWithSeeds_seed_{slot} s)',
        f'#print axioms {stem}_seed',
        f'theorem {stem}_broadcast (s t : Store) (h : {label}SeededDenoteWithInputs s = some t) :',
        f'    t {out} = Tensor.mkShape (t {x}).shape (fun _ => 1) := by',
        f'  rw [{stem}_read ({label}InitialWithSeeds s) t h, {stem}_seed s t h]',
        f'  exact unitSeed_bw_sum (t {x})',f'#print axioms {stem}_broadcast']
    return '\n'.join(proof)+'\n',dict(world=label,source_index=i,execution_index=k,
        seed=seed,input_refs=[list(r) for r in cell.inputs],output_refs=[list(r) for r in cell.outputs],
        bw_writer=bw_writer,fw_writer=fw_writer,operand_nonwrite_source_indices=sequence[k:],
        theorems=[stem+s for s in ('_read','_seed','_broadcast')])


def render(worlds,config,handoff_root):
    if [w[-1] for w in worlds]!=['sm','pm']:
        raise ValueError('bw-sum complete ordered SM/PM sources required')
    sm,pm=worlds
    authenticated=seeds.load_bundle(config,sm[0],pm[0],sm[1],pm[1],handoff_root)
    proof=[];rows=[]
    for view,cells,snapshot,order,label in worlds:
        for slot,seed in enumerate(authenticated['inventories'][label]):
            text,row=_read(view,cells,snapshot,order,label,seed,slot);proof.append(text);rows.append(row)
    return ''.join(proof),dict(reads=rows,inventories=authenticated['inventories'],runs=authenticated['runs'],
        proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False)
