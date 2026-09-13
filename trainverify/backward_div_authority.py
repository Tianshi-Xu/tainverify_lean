"""Original BW_div [G, saved input X] -> [dX] for a raw scalar divisor.

This record is not a proof, nor a Torch refinement or distributed gradient claim.
"""

from math import isfinite

from trainverify.backward_linear_authority import _ir_identity
from Verdict.runtime_lineage import _same_typed


def _fail(reason):
    raise ValueError('bw-div ' + reason)


def bind(cells, source_index):
    from nnscaler.ir.operator import IRBpOperation
    if type(source_index) is not int or not 0 <= source_index < len(cells):
        _fail('invalid source index')
    cell = cells[source_index]
    if not isinstance(cell.ir, IRBpOperation) or cell.opname.name != 'BW_div':
        _fail('original typed backward operation required')
    paired = [(i, c) for i, c in enumerate(cells) if c.ir is cell.ir.mirror
              and (c.node.wtype, c.rank, c.mb) == (cell.node.wtype, cell.rank, cell.mb)]
    if len(paired) != 1 or paired[0][0] >= source_index:
        _fail('original forward mirror order/identity mismatch')
    fi, fw = paired[0]
    if fw.opname.name != 'FW_div' or fw.ir.signature != 'torch.div':
        _fail('original forward function/opcode mismatch')
    if cell.ir.signature != 'torch.autograd.grad':
        _fail('original backward function mismatch')
    if (len(cell.inputs) != 2 or len(cell.outputs) != 1
            or len(cell._input_irs) != 2 or len(cell._output_irs) != 1
            or len(fw.inputs) != 1 or len(fw.outputs) != 1
            or len(fw._input_irs) != 1 or len(fw._output_irs) != 1):
        _fail('complete ordered [G,saved_input] -> [dx] ports required')
    if not _same_typed([tuple(r) for r in cell.inputs[1:]], [tuple(r) for r in fw.inputs]):
        _fail('saved primal input fullref/version mismatch')
    for obj, name in ((cell, 'BW.' + fw.ir.name), (fw, fw.ir.name)):
        if not _same_typed(tuple(obj.node), (obj.wtype.value, obj.rank, obj.mb, obj.ir.cid, name)):
            _fail('original typed node/IR identity mismatch')
        for source_kwargs in (obj.kwargs, obj.ir.kwargs):
            if (set(source_kwargs) - {'rounding_mode', '__consts'}
                    or source_kwargs.get('rounding_mode') is not None):
                _fail('unsupported rounding mode/source kwargs')
        # __consts is an expansion-only field, absent on some raw IRs.
        kwargs = {k: v for k, v in obj.kwargs.items() if k != '__consts'}
        raw = {k: v for k, v in obj.ir.kwargs.items() if k != '__consts'}
        if not _same_typed(kwargs, raw):
            _fail('original IR/cell kwargs mismatch')
        if not _same_typed(kwargs, {k: v for k, v in fw.kwargs.items() if k != '__consts'}):
            _fail('original FW/BW kwargs mismatch')
        for refs, irs in ((obj.inputs, obj._input_irs), (obj.outputs, obj._output_irs)):
            for ref, ir in zip(refs, irs, strict=True):
                expected = (obj.node.wtype, obj.rank, -1 if ir.is_attr() else obj.mb, ir.tid)
                if not _same_typed(tuple(ref)[:4], expected) or type(ref.v) is not int or ref.v < 0:
                    _fail('ordered source fullref/IR identity mismatch')
    raw_fwi = list(fw.ir.inputs())
    if len(raw_fwi) != 2:
        _fail('original forward tensor/scalar argument arity mismatch')
    raw_divisor = raw_fwi[1]
    from nnscaler.ir.cten import IRObject
    # Only a constant non-tensor IRObject can carry a scalar literal. In
    # particular, never unwrap an IRTensor merely because it has a .value.
    if type(raw_divisor) is IRObject:
        if raw_divisor.is_constant is not True:
            _fail('dynamic IRObject divisor lacks literal authority')
        raw_divisor = raw_divisor.value
    # Validate the original literal before Nat lowering; int(4.5) is not evidence.
    if (type(raw_divisor) not in (int, float) or raw_divisor <= 0
            or (type(raw_divisor) is float and
                (not isfinite(raw_divisor) or not raw_divisor.is_integer()))):
        _fail('unsupported positive finite integral scalar divisor')
    divisor = int(raw_divisor)
    for obj in (cell, fw):
        if (not _same_typed(obj.kwargs.get('__consts'), [raw_divisor])
                or not _same_typed(obj.ir.kwargs.get('__consts', [raw_divisor]), [raw_divisor])):
            _fail('original raw divisor/constant metadata typed identity mismatch')
    fwi, fwo = raw_fwi[:1], list(fw.ir.outputs())
    bwi, bwo = list(cell.ir.inputs()) + fwi, list(cell.ir.outputs())
    if len(fwi) != 1 or len(fwo) != 1 or len(bwi) != 2 or len(bwo) != 1:
        _fail('original mirror arity mismatch')
    for actual, expected in ((cell._input_irs, bwi), (cell._output_irs, bwo),
                             (fw._input_irs, fwi), (fw._output_irs, fwo),
                             ([cell._input_irs[0]], [fwo[0].grad]),
                             (cell._output_irs, [fwi[0].grad])):
        if not _same_typed([_ir_identity(t) for t in actual], [_ir_identity(t) for t in expected]):
            _fail('original mirror saved/gradient metadata mismatch')
    shapes = [tuple(t.shape) for t in (*cell._input_irs, *cell._output_irs,
                                       *fw._input_irs, *fw._output_irs)]
    if (any(not shape or any(type(d) is not int or d <= 0 for d in shape) for shape in shapes)
            or any(not _same_typed(shape, shapes[0]) for shape in shapes[1:])):
        _fail('original equal positive-rank g/x/dx shapes required')
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
    return dict(source_index=source_index, fw_source_index=fi,
                bw_node=list(cell.node), fw_node=list(fw.node),
                inputs=[list(r) for r in cell.inputs], outputs=[list(r) for r in cell.outputs],
                saved_inputs=[list(r) for r in fw.inputs],
                input_roles=['cotangent', 'saved_input'], output_roles=['dx'],
                input_shapes=[list(t.shape) for t in cell._input_irs],
                output_shapes=[list(t.shape) for t in cell._output_irs],
                fw_signature=fw.ir.signature, bw_signature=cell.ir.signature,
                fw_kwargs=dict(fw.kwargs), bw_kwargs=dict(cell.kwargs),
                raw_divisor=raw_divisor, divisor=divisor, derivative='G / divisor',
                obligations=['cotangent provenance', 'saved primal input source identity'],
                proof_admissible=False, kernel_value_proved=False,
                public_complete=False, torch_refinement=False)
