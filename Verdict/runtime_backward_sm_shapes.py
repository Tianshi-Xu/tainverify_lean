"""Sparse original-run SM shapes; no alternate evaluator or full-prefix rebuild.

The emitted Lean is a candidate until separately kernel checked. Parameter
shapes are explicit FINAL-store caller obligations, not capture-proved facts.
Source tensor shapes are used to select/check schemas, never as proof axioms.
"""
from typing import NoReturn

from Verdict import graph_to_lean, runtime_schedule, runtime_world
from Verdict.runtime_backward_linear_reads import _writer, render_read
from Verdict.runtime_lineage import _same_typed
from trainverify.backward_linear_authority import _ir_identity


_SIGNATURES = {
    'DATALOADER': 'next', 'FW_embedding': 'nnscaler.runtime.function.embedding',
    'FW_add': 'torch.add', 'FW_multiref': 'nnscaler.runtime.function.multiref',
    'FW_view': 'torch.Tensor.view', 'FW_linear': 'torch.nn.functional.linear',
    'FW_layernorm': 'nnscaler.runtime.function.layer_norm',
    'FW_gelu': 'torch.nn.functional.gelu', 'BW_sum': 'torch.autograd.grad',
    'FW_sum': 'torch.sum',
}


def _fail(message) -> NoReturn:
    raise ValueError('bw-sm-shapes ' + message)


def _bind(view, cells, snapshot, index, sequence):
    """Join live IR -> cell -> writer/export -> ordered lowered ports afresh."""
    cell = cells[index]; node = cell.node; op = cell.opname.name
    if op not in _SIGNATURES or cell.ir is None or cell.ir.signature != _SIGNATURES[op]:
        _fail('unsupported original operation/signature')
    name = ('BW.' + cell.ir.mirror.name if op == 'BW_sum' else
            type(cell.ir).__name__ if op == 'DATALOADER' else cell.ir.name)
    if not _same_typed(tuple(node), (cell.wtype.value, cell.rank, cell.mb, cell.ir.cid, name)):
        _fail('original node/IR identity mismatch')
    if (str(view.node_opname(node)).split('.')[-1] != op
            or not _same_typed(view.node_kwargs(node), cell.kwargs)
            or not _same_typed(cell.kwargs, cell.ir.kwargs)):
        _fail('original opcode/kwargs mismatch')
    if any(node in getattr(view, key, {}) for key in ('collective_scopes', 'chunk_scopes', 'wred_scopes')):
        _fail('ordinary source scope required')
    params, unsupported = runtime_world._ordinary(view, node, graph_to_lean._get_node_params)
    if unsupported and op != 'DATALOADER':
        _fail(unsupported)
    expected = (list(cell.ir.kwargs['size']) if op == 'FW_view' else
                [len(cell.outputs)] if op == 'FW_multiref' else [])
    if not _same_typed(params, expected):
        _fail('original params mismatch')
    if op == 'FW_view' and (not expected or any(type(x) is not int or x <= 0 for x in expected)):
        _fail('nonempty positive explicit view shape required')
    if op == 'FW_multiref' and not _same_typed(cell.kwargs.get('times'), len(cell.outputs)):
        _fail('original multiref multiplicity mismatch')
    if op == 'FW_add' and not _same_typed(cell.kwargs.get('alpha', 1), 1):
        _fail('unsupported addition alpha')
    if op == 'FW_embedding' and cell.kwargs['stop'] != cell._input_irs[1].shape[0]:
        _fail('embedding must cover original vocabulary')
    originals = list(cell.ir.inputs())
    if op == 'BW_sum':
        from nnscaler.ir.operator import IRBpOperation
        if not isinstance(cell.ir, IRBpOperation) or cell.ir.mirror.signature != 'torch.sum':
            _fail('original BW_sum mirror required')
        pairs = [j for j,c in enumerate(cells) if c.ir is cell.ir.mirror
                 and (c.rank,c.mb,c.node.wtype) == (cell.rank,cell.mb,node.wtype)]
        if len(pairs) != 1 or sequence.index(pairs[0]) >= sequence.index(index):
            _fail('original BW_sum mirror order/identity mismatch')
        fw = cells[pairs[0]]
        _bind(view, cells, snapshot, pairs[0], sequence)
        if not _same_typed(list(cell.inputs[1:]), list(fw.inputs)):
            _fail('original BW_sum saved fullref mismatch')
        originals += list(cell.ir.mirror.inputs())
        if not _same_typed([_ir_identity(t) for t in cell._input_irs[:1]],
                           [_ir_identity(cell.ir.mirror.output(0).grad)]):
            _fail('original BW_sum gradient identity mismatch')
        if not _same_typed([_ir_identity(t) for t in cell._output_irs],
                           [_ir_identity(cell.ir.mirror.input(0).grad)]):
            _fail('original BW_sum output gradient identity mismatch')
    for side, raw in [('inputs', originals), ('outputs', list(cell.ir.outputs()))]:
        irs = getattr(cell, '_' + side[:-1] + '_irs')
        refs = getattr(cell, side); ts = getattr(view, 'node_' + side)(node)
        # Loader raw inputs are the non-tensor iterator, not graph input ports.
        if not (op == 'DATALOADER' and side == 'inputs'):
            if not _same_typed([_ir_identity(t) for t in irs], [_ir_identity(t) for t in raw]):
                _fail('original ordered IR metadata mismatch')
        if not _same_typed([tuple(view.source_tensor(t)) for t in ts], [tuple(r) for r in refs]):
            _fail('lowered ordered fullref mismatch')
        if not _same_typed([tuple(view.tensor_shape(t)) for t in ts], [tuple(t.shape) for t in irs]):
            _fail('original lowered shape mismatch')
        for ref, ir in zip(refs, irs, strict=True):
            if not _same_typed(tuple(ref)[:4], (node.wtype,cell.rank,-1 if ir.is_attr() else cell.mb,ir.tid)) or type(ref.v) is not int or ref.v < 0:
                _fail('original fullref/IR identity mismatch')
    k = sequence.index(index)
    inputs = [t.tid for t in view.node_inputs(node)]
    if any(set(inputs) & {t.tid for t in view.node_outputs(cells[j].node)} for j in sequence[k:]):
        _fail('operand written by selected node or full execution suffix')
    return dict(source_index=index, execution_index=k, op=op, params=params,
                writer=_writer(snapshot,cells,index), input_tids=inputs,
                output_tids=[t.tid for t in view.node_outputs(node)],
                input_refs=[list(r) for r in cell.inputs], output_refs=[list(r) for r in cell.outputs],
                operand_nonwrite_source_indices=sequence[k:])


def _split(k):
    return ['  · calc', f'      smInputRequests = smInputRequests.take {k} ++ smInputRequests.drop {k} := (List.take_append_drop {k} smInputRequests).symm', '      _ = _ := rfl']


def _read(row, out, port, rank):
    i=row['source_index']; k=row['execution_index']; op=row['op']; xs=row['input_tids']; ps=row['params']
    name=f'backwardSMRead_{i}_{out}'
    a=[f'(t {x})' for x in xs]
    common=f'smGraph smScope smPeers smGraph.nodes\n    smInputRequests (smInputRequests.take {k}) (smInputRequests.drop {k+1}) smNode_{i}'
    pre=[f'theorem {name} (s t : Store) (h : smDenoteWithInputs s = some t) :']
    if op=='DATALOADER':
        value=f'smNode_{i}_port{port}'
        member='List.mem_cons_self'
        for _ in range(port):
            member=f'List.mem_cons_of_mem _ ({member})'
        return pre+[f'    t {out} = {value} := by', f'  apply SourceInitialInputRead.input_value_of_split {common} smNode_{i}_feed', f'    s t {out} {value} ?_ rfl smNode_{i}_contract ({member}) h']+_split(k)+[f'#print axioms {name}']
    table={
        'FW_embedding':('SourceEmbeddingRead.embedding_value_of_split','fw_embedding '+' '.join(a)),
        'FW_linear':('SourceLinearRead.linear_value_of_split','fw_linear '+' '.join(a)),
        'FW_add':('SourceAddRead.add_value_of_split','elemwiseAdd '+' '.join(a)),
        'FW_layernorm':('SourceLayernormRead.layernorm_value_of_split','fw_layernorm '+' '.join(a)),
        'BW_sum':('SourceBWSumRead.bw_sum_value_of_split','bw_sum '+' '.join(a)),
        'FW_view':('SourceLayoutRead.view_value_of_split',f'fw_view {ps} '+ ' '.join(a)),
        'FW_multiref':('SourceMultirefRead.multiref_value_of_split',a[0]),
    }
    if op=='FW_gelu':
        x=xs[0]
        pre += [f'    t {out} = fw_gelu (t {x}) := by',
                f'  apply SourceValueRead.node_value_of_split {common} {out} [{x}] (fun a => fw_gelu (a {x})) s t ?_ (by decide) ?_ ?_ ?_ h']
        pre += _split(k)
        pre += [f'  · intro tid htid',f'    have heq : tid = {x} := List.mem_singleton.mp htid', '    subst tid',f'    change ∀ row ∈ smInputRequests.drop {k}, {x} ∉ row.1.outs','    decide',
                '  · intro a b hstep',f'    have hs : SourceScopedEval.stepWithInputs smGraph (smScope smNode_{i}) (smPeers smNode_{i}) a smNode_{i} none = some (applyNode smGraph a smNode_{i}) := by',
                f'      change SourceScopedEval.stepWithInputs smGraph .global (smPeers smNode_{i}) a smNode_{i} none = _',
                '      rw [SourceScopedEval.stepWithInputs_ordinary _ _ _ _ _ (by decide)]',
                '      exact SourceScopedEval.step_global _ _ _ _ (by decide)',
                f'    have hb : applyNode smGraph a smNode_{i} = b := Option.some.inj (hs.symm.trans hstep)',
                '    rw [← hb]', f'    exact applyNode_fw_gelu_out smGraph a {rank} {x} {out}',
                '  · intro a b hab',f'    rw [hab {x} List.mem_cons_self]',f'#print axioms {name}']
        return pre
    lemma, expr=table[op]
    args=' '.join(map(str,xs+[out]))
    if op=='FW_view': args+=f' {ps[0]} {ps[1:]}'
    if op=='FW_multiref': args=f'{xs[0]} {row["output_tids"]} {out}'
    extra=' (by decide)' if op=='FW_multiref' else ''
    pre += [f'    t {out} = {expr} := by',f'  apply {lemma} {common}',f'    {rank} {args} s t rfl ?_ rfl '+ ' '.join(' ?_' for _ in xs)+extra+' h']
    pre += _split(k)
    for x in xs:
        pre += [f'  · change ∀ row ∈ smInputRequests.drop {k}, {x} ∉ row.1.outs','    decide']
    return pre+[f'#print axioms {name}']


def render(worlds, source_index=None):
    """Project the first SM BW_linear by default; unsupported chains fail closed.

    Caller imports the unchanged RuntimeWorldData and operator read modules.
    No parameter frame, seeded success, Torch refinement, or kernel acceptance
    is claimed here. A seeded caller instantiates s with smInitialWithSeeds s.
    """
    sm=[w for w in worlds if w[-1]=='sm']
    if len(sm)!=1: _fail('unique original SM world required')
    view,cells,snapshot,order,label=sm[0]
    runtime_world._authenticate(view,cells,graph_to_lean)
    runtime_schedule.validate(view,order['execution_to_source'])
    sequence=order['execution_to_source']
    if source_index is None:
        source_index=next((i for i in sequence if cells[i].opname.name=='BW_linear'),None)
    _,linear=render_read(view,cells,snapshot,source_index,order,label)
    g,x,w=linear['input_tids']
    writers={t.tid:i for i in sequence for t in view.node_outputs(cells[i].node)}
    tensors={t.tid:t for t in view.tensors()}
    rows={}; shapes={}; leaves={}; active=set()
    def visit(tid):
        if tid in shapes: return shapes[tid]
        if tid in active: _fail('cyclic shape dependency')
        active.add(tid)
        if tid not in writers:
            ref=view.source_tensor(tensors[tid])
            matches=[ir for c in cells for r,ir in zip(c.inputs,c._input_irs,strict=True) if tuple(r)==tuple(ref)]
            if not matches or any(not ir.is_param() or ir.is_grad() for ir in matches) or ref.v!=0:
                _fail('shape leaf is not an original unwritten parameter')
            shape=list(view.tensor_shape(tensors[tid]))
            leaves[tid]=dict(tid=tid,shape=shape,ref=list(ref),obligation='final-store parameter shape; caller must derive via initial parameter relation/frame')
        else:
            i=writers[tid]
            if i not in rows:
                rows[i]=_bind(view,cells,snapshot,i,sequence)
            row=rows[i]
            op=row['op']; ins=row['input_tids']
            if op=='DATALOADER': shape=list(view.tensor_shape(tensors[tid])); deps=[]
            elif op=='FW_view': shape=row['params']; deps=[]
            elif op in ('FW_multiref','FW_layernorm','FW_gelu'): deps=ins[:1]; shape=visit(ins[0])
            elif op=='FW_embedding':
                deps=ins; ids,weight=map(visit,ins); shape=ids+[weight[-1]]
            elif op=='FW_linear':
                deps=ins; inp,weight=map(visit,ins)
                if len(inp) not in (2,3) or len(weight)!=2 or inp[-1]!=weight[1]: _fail('unsupported linear shape contraction')
                shape=inp[:-1]+[weight[0]]
            elif op=='FW_add':
                deps=ins; left,right=map(visit,ins)
                if left!=right: _fail('only equal-shape residual addition supported')
                shape=left
            elif op=='BW_sum': deps=ins[1:]; shape=visit(ins[1])
            else: _fail('unsupported sparse shape producer '+op)
            if shape!=list(view.tensor_shape(tensors[tid])): _fail('derived/source output shape mismatch')
            row.setdefault('shape_outputs',{})[tid]=dict(shape=shape,dependencies=deps)
        shapes[tid]=list(shape); active.remove(tid); return shapes[tid]
    visit(x); visit(g)
    sumrow=rows[writers[g]]
    if sumrow['op']!='BW_sum': _fail('direct original BW_sum cotangent required')
    primal=sumrow['input_tids'][1]
    parameters=[leaves[t] for t in sorted(leaves)]
    ordered=[rows[i] for i in sequence if i in rows]
    text=['-- Sparse SM candidate: kernel checking and parameter-frame discharge are external.',
          'def backwardSMFinalParameterShapes (t : Store) : Prop :=',
          '  '+ ' ∧ '.join(f'(t {p["tid"]}).shape = {p["shape"]}' for p in parameters)]
    for row in ordered:
        for tid in row['shape_outputs']:
            text += _read(row,tid,row['output_tids'].index(tid),cells[row['source_index']].rank)
    text += ['theorem backwardSMShapes (s t : Store) (hp : backwardSMFinalParameterShapes t)',
             '    (h : smDenoteWithInputs s = some t) :',
             '    '+' ∧ '.join(f'(t {tid}).shape = {shapes[tid]}' for tid in (x,primal,g))+' := by',
             '  rcases hp with ⟨'+', '.join(f'hp{p["tid"]}' for p in parameters)+'⟩']
    def hshape(tid): return f'hp{tid}' if tid in leaves else f'hsh{tid}'
    for row in ordered:
        i=row['source_index']; ins=row['input_tids']; op=row['op']
        for tid,info in row['shape_outputs'].items():
            sh=info['shape']; rd=f'backwardSMRead_{i}_{tid} s t h'
            text += [f'  have hsh{tid} : (t {tid}).shape = {sh} := by',f'    rw [{rd}]']
            if op in ('FW_view','DATALOADER'): text+=['    rfl']
            elif op=='FW_multiref': text += [f'    exact {hshape(ins[0])}']
            elif op=='FW_layernorm': text += [f'    exact (SourceScopedPrefix.layernorm_shape _ _ _).trans {hshape(ins[0])}']
            elif op=='FW_gelu': text += [f'    exact (fw_gelu_shape _).trans {hshape(ins[0])}']
            elif op=='FW_embedding': text += [f'    rw [fw_embedding_shape, {hshape(ins[0])}, {hshape(ins[1])}]','    rfl']
            elif op=='FW_add': text += [f'    exact elemwiseAdd_shape_of_shapes _ _ {sh} {hshape(ins[0])} {hshape(ins[1])}']
            elif op=='FW_linear':
                ish=shapes[ins[0]]; lemma='fw_linear_3d_shape' if len(ish)==3 else 'SourceScopedPrefix.linear_shape_2d'
                text += [f'    exact {lemma} '+ ' '.join(map(str,ish+[sh[-1]]))+f' _ _ {hshape(ins[0])} {hshape(ins[1])}']
            elif op=='BW_sum': text += [f'    change (t {ins[1]}).shape = {sh}',f'    exact {hshape(ins[1])}']
    text += ['  exact ⟨'+', '.join(hshape(tid) for tid in (x,primal,g))+'⟩','#print axioms backwardSMShapes']
    return '\n'.join(text)+'\n',dict(source_indices=[r['source_index'] for r in ordered],
        view_anchors=[r['source_index'] for r in ordered if r['op']=='FW_view'],reads=ordered,
        parameter_shapes=parameters,linear_binding=linear,
        conclusions=[dict(tid=tid,shape=shapes[tid]) for tid in (x,primal,g)],
        obligations=['exact original RuntimeWorldData imports and source/fullref/order binding',
                     'original successful run (seeded caller may substitute smInitialWithSeeds)',
                     'backwardSMFinalParameterShapes t: derive from initial parameter values and frame',
                     'serial Lean kernel and axiom checking; candidate not compiled here'],
        proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False)
