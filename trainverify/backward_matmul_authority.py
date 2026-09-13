"""Original BW_matmul [G,X,Y] -> [dX,dY]; both saved values are primal inputs.

Only positive matrix dimensions with identical batch prefixes are certified.
No Torch vector promotion or batch broadcasting/reduction is claimed.
"""
from trainverify.backward_linear_authority import _ir_identity
from Verdict.runtime_lineage import _same_typed


def _fail(reason):
    raise ValueError('bw-matmul ' + reason)


def bind(cells, source_index):
    from nnscaler.ir.operator import IRBpOperation
    if type(source_index) is not int or not 0 <= source_index < len(cells):
        _fail('invalid source index')
    cell = cells[source_index]
    if not isinstance(cell.ir, IRBpOperation) or cell.opname.name != 'BW_matmul':
        _fail('original typed backward operation required')
    paired = [(i, c) for i, c in enumerate(cells) if c.ir is cell.ir.mirror
              and (c.node.wtype, c.rank, c.mb) == (cell.node.wtype, cell.rank, cell.mb)]
    if len(paired) != 1 or paired[0][0] >= source_index:
        _fail('original forward mirror order/identity mismatch')
    fi, fw = paired[0]
    if fw.opname.name != 'FW_matmul' or fw.ir.signature != 'torch.matmul':
        _fail('original forward function/opcode mismatch')
    if cell.ir.signature != 'torch.autograd.grad':
        _fail('original backward function mismatch')
    if (len(cell.inputs) != 3 or len(cell.outputs) != 2
            or len(cell._input_irs) != 3 or len(cell._output_irs) != 2
            or len(fw.inputs) != 2 or len(fw.outputs) != 1
            or len(fw._input_irs) != 2 or len(fw._output_irs) != 1):
        _fail('complete ordered [G,savedX,savedY] -> [dX,dY] ports required')
    if not _same_typed([tuple(r) for r in cell.inputs[1:]], [tuple(r) for r in fw.inputs]):
        _fail('saved primal fullref/version mismatch')
    for obj, name in ((cell, 'BW.' + fw.ir.name), (fw, fw.ir.name)):
        if not _same_typed(tuple(obj.node), (obj.wtype.value, obj.rank, obj.mb, obj.ir.cid, name)):
            _fail('original typed node/IR identity mismatch')
        kwargs = dict(obj.kwargs)
        if set(kwargs) - {'__consts'} or not _same_typed(kwargs.get('__consts', []), []):
            _fail('unsupported source kwargs')
        kwargs.pop('__consts', None)
        raw = dict(obj.ir.kwargs)
        if not _same_typed(raw.get('__consts', []), []):
            _fail('unsupported raw constants')
        raw.pop('__consts', None)
        if not _same_typed(kwargs, raw):
            _fail('original IR/cell kwargs mismatch')
        if not _same_typed(kwargs, {k: v for k, v in fw.kwargs.items() if k != '__consts'}):
            _fail('original FW/BW kwargs mismatch')
        for refs, irs in ((obj.inputs, obj._input_irs), (obj.outputs, obj._output_irs)):
            for ref, ir in zip(refs, irs, strict=True):
                expected = (obj.node.wtype, obj.rank, -1 if ir.is_attr() else obj.mb, ir.tid)
                if not _same_typed(tuple(ref)[:4], expected) or type(ref.v) is not int or ref.v < 0:
                    _fail('ordered source fullref/IR identity mismatch')
    fwi, fwo = list(fw.ir.inputs()), list(fw.ir.outputs())
    bwi, bwo = list(cell.ir.inputs()) + fwi, list(cell.ir.outputs())
    if len(fwi) != 2 or len(fwo) != 1 or len(bwi) != 3 or len(bwo) != 2:
        _fail('original mirror arity mismatch')
    for actual, expected in ((cell._input_irs, bwi), (cell._output_irs, bwo),
                             (fw._input_irs, fwi), (fw._output_irs, fwo),
                             ([cell._input_irs[0]], [fwo[0].grad]),
                             (cell._output_irs, [t.grad for t in fwi])):
        if not _same_typed([_ir_identity(t) for t in actual], [_ir_identity(t) for t in expected]):
            _fail('original mirror saved/gradient metadata mismatch')
    for ref, ir in zip(cell.inputs, cell._input_irs, strict=True):
        if ref.v == 0 and not (ir.is_attr() is True and ir.is_grad() is False):
            _fail('external activation/cotangent lacks original writer authority')
        writers = [c for c in cells[:source_index]
                   if any(_same_typed(tuple(r), tuple(ref)) for r in c.outputs)]
        if ref.v != 0 and len(writers) != 1:
            _fail('input writer/version missing/ambiguous')
    watched = [tuple(r) for r in (*cell.inputs, *cell.outputs)]
    if any(_same_typed(tuple(r), key) for later in cells[source_index + 1:]
           for r in later.outputs for key in watched):
        _fail('input/output fullref suffix overwrite')
    shapes = [tuple(t.shape) for t in (*cell._input_irs, *cell._output_irs,
                                      *fw._input_irs, *fw._output_irs)]
    if any(not sh or any(type(n) is not int or n <= 0 for n in sh) for sh in shapes):
        _fail('positive nonempty original shapes required')
    g, x, y, dx, dy, fx, fy, fz = shapes
    validate_shapes(g, x, y)
    if x != fx or y != fy or g != fz or dx != x or dy != y:
        _fail('original gradient/primal output shape mismatch')
    if _same_typed(tuple(cell.outputs[0]), tuple(cell.outputs[1])):
        _fail('distinct original output ports required')
    return dict(source_index=source_index, fw_source_index=fi,
                bw_node=list(cell.node), fw_node=list(fw.node),
                inputs=[list(r) for r in cell.inputs], outputs=[list(r) for r in cell.outputs],
                saved_inputs=[list(r) for r in fw.inputs],
                input_roles=['cotangent', 'saved_left', 'saved_right'], output_roles=['dx', 'dy'],
                input_ir_identities=[_ir_identity(t) for t in cell._input_irs],
                output_ir_identities=[_ir_identity(t) for t in cell._output_irs],
                input_shapes=[list(g), list(x), list(y)], output_shapes=[list(dx), list(dy)],
                batch_prefix=list(x[:-2]), batch_broadcast=False,
                fw_signature=fw.ir.signature, bw_signature=cell.ir.signature,
                fw_kwargs=dict(fw.kwargs), bw_kwargs=dict(cell.kwargs),
                derivative=['G @ transpose_last_two(Y)', 'transpose_last_two(X) @ G'],
                obligations=['cotangent provenance', 'both saved primal value reconstructions',
                             'distributed contribution ownership; no parameter-gradient claim'],
                proof_admissible=False, kernel_value_proved=False,
                public_complete=False, torch_refinement=False)


def validate_shapes(g, x, y):
    """Fail closed outside Denote's same-batch-prefix matrix contraction domain."""
    if any(len(sh) < 2 or any(type(d) is not int or d <= 0 for d in sh) for sh in (g, x, y)):
        _fail('positive matrix dimensions required; vectors unsupported')
    if tuple(x[:-2]) != tuple(y[:-2]) or tuple(g[:-2]) != tuple(x[:-2]):
        _fail('batch broadcasting unsupported: requires reduction absent from Denote')
    if x[-1] != y[-2] or tuple(g[-2:]) != (x[-2], y[-1]):
        _fail('contraction/cotangent dimensions mismatch')
