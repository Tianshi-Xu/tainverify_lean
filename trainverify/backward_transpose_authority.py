"""Authenticate original BW_transpose [G,saved FW input] as reverse axis permutation.

Dims determine the value permutation; saved tensor values are not a premise.
This source-domain contract is not Torch refinement or model-gradient closure.
"""
from trainverify.backward_linear_authority import _ir_identity
from Verdict.runtime_lineage import _same_typed


def _fail(reason):
    raise ValueError('bw-transpose ' + reason)


def bind(cells, source_index):
    from nnscaler.ir.operator import IRBpOperation
    if type(source_index) is not int or not 0 <= source_index < len(cells):
        _fail('invalid source index')
    cell = cells[source_index]
    if not isinstance(cell.ir, IRBpOperation) or cell.opname.name != 'BW_transpose':
        _fail('original typed backward operation required')
    paired = [(i, c) for i, c in enumerate(cells) if c.ir is cell.ir.mirror
              and (c.node.wtype, c.rank, c.mb) == (cell.node.wtype, cell.rank, cell.mb)]
    if len(paired) != 1 or paired[0][0] >= source_index:
        _fail('original forward mirror order/identity mismatch')
    fi, fw = paired[0]
    if fw.opname.name != 'FW_transpose' or fw.ir.signature != 'torch.transpose':
        _fail('original forward function/opcode mismatch')
    if cell.ir.signature != 'torch.autograd.grad':
        _fail('original backward function mismatch')
    if (len(cell.inputs) != 2 or len(cell.outputs) != 1
            or len(cell._input_irs) != 2 or len(cell._output_irs) != 1
            or len(fw.inputs) != 1 or len(fw.outputs) != 1
            or len(fw._input_irs) != 1 or len(fw._output_irs) != 1):
        _fail('complete ordered [G,savedX] -> [dX] ports required')
    if not _same_typed([tuple(r) for r in cell.inputs[1:]], [tuple(r) for r in fw.inputs]):
        _fail('saved primal fullref/version mismatch')
    for obj, name in ((cell, 'BW.' + fw.ir.name), (fw, fw.ir.name)):
        if not _same_typed(tuple(obj.node), (obj.wtype.value, obj.rank, obj.mb, obj.ir.cid, name)):
            _fail('original typed node/IR identity mismatch')
        kwargs = dict(obj.kwargs)
        if set(kwargs) - {'dim0', 'dim1', '__consts'} or not _same_typed(kwargs.get('__consts', []), []):
            _fail('unsupported source kwargs')
        kwargs.pop('__consts', None)
        raw = dict(obj.ir.kwargs)
        if not _same_typed(raw.get('__consts', []), []):
            _fail('unsupported raw constants')
        raw.pop('__consts', None)
        if not _same_typed(kwargs, raw):
            _fail('original IR/cell kwargs mismatch')
        if not _same_typed(kwargs, {k: v for k, v in fw.kwargs.items() if k != '__consts'}):
            _fail('original FW/BW dimension kwargs mismatch')
        for refs, irs in ((obj.inputs, obj._input_irs), (obj.outputs, obj._output_irs)):
            for ref, ir in zip(refs, irs, strict=True):
                expected = (obj.node.wtype, obj.rank, -1 if ir.is_attr() else obj.mb, ir.tid)
                if not _same_typed(tuple(ref)[:4], expected) or type(ref.v) is not int or ref.v < 0:
                    _fail('ordered source fullref/IR identity mismatch')
    fwi, fwo = list(fw.ir.inputs()), list(fw.ir.outputs())
    bwi, bwo = list(cell.ir.inputs()) + fwi, list(cell.ir.outputs())
    if len(fwi) != 1 or len(fwo) != 1 or len(bwi) != 2 or len(bwo) != 1:
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
    g, x, dx, fx, fy = shapes
    if g != fy or x != fx or dx != x or len(g) != len(x):
        _fail('original gradient/input/output shape mismatch')
    dims = [fw.kwargs.get('dim0'), fw.kwargs.get('dim1')]
    ndim = len(x)
    if any(type(d) is not int or not -ndim <= d < ndim for d in dims):
        _fail('dimensions must be strict integers within Torch non-scalar rank bounds')
    normalized = [d % ndim for d in dims]
    forward = list(x)
    d0, d1 = normalized
    forward[d0], forward[d1] = forward[d1], forward[d0]
    if tuple(forward) != fy:
        _fail('original transpose dimensions disagree with FW output')
    if any(t.is_grad() is not want for t, want in
           zip((*cell._input_irs, *cell._output_irs, *fw._input_irs, *fw._output_irs),
               (True, False, True, False, False), strict=True)):
        _fail('source gradient/primal role flags mismatch')
    return dict(source_index=source_index, fw_source_index=fi,
                bw_node=list(cell.node), fw_node=list(fw.node),
                inputs=[list(r) for r in cell.inputs], outputs=[list(r) for r in cell.outputs],
                saved_inputs=[list(r) for r in fw.inputs],
                input_roles=['cotangent', 'saved_input'], output_roles=['dx'],
                target_shape=list(x), cotangent_shape=list(g), forward_shape=list(fy),
                fw_signature=fw.ir.signature, bw_signature=cell.ir.signature,
                fw_kwargs=dict(fw.kwargs), bw_kwargs=dict(cell.kwargs),
                derivative='transpose(cotangent, dim0, dim1)',
                source_dims=dims, params=normalized,
                support='positive nonempty shapes; arbitrary rank; normalized valid signed axes',
                saved_value_premise=False,
                proof_admissible=False, kernel_value_proved=False,
                public_complete=False, torch_refinement=False)
