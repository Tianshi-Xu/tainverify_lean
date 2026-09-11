"""Bind a bias-free BW_linear to its original nnScaler mirror and saved refs.

This consumes live expanded source cells, not a renderer descriptor. The result
is an interface obligation record, never a proof or a substitute for the caller's
whole-model/source authority. It does not authenticate loss scaling or autograd
execution. No graph mutation or capture is performed.
"""


def _ir_identity(t):
    from nnscaler.ir.tensor import IRSubTensor
    if not isinstance(t, IRSubTensor):
        raise ValueError('bw-linear complete original tensor identity required')
    return (t.tid, t.parent.tid, t.parent.name, tuple(t.shape), tuple(t.parent.shape),
            tuple(t.indmap), tuple(t.valmap), t.is_param(), t.is_grad(), t.is_attr())


def bind(cells, source_index):
    """Return the local [dY, X, W] -> [dX, dW] source contract.

    Rank2/rank3 bias-free linear only; reduction is over all leading X axes.
    The caller must establish cotangent provenance and cross-store input
    relations before applying distributed dX/dW theorems.
    """
    from nnscaler.ir.operator import IRBpOperation

    if type(source_index) is not int or not 0 <= source_index < len(cells):
        raise ValueError('bw-linear invalid source index')
    cell = cells[source_index]
    if not isinstance(cell.ir, IRBpOperation) or cell.opname.name != 'BW_linear':
        raise ValueError('bw-linear original typed backward operation required')
    paired = [(i, c) for i, c in enumerate(cells) if c.ir is cell.ir.mirror
              and (c.node.wtype, c.rank, c.mb) == (cell.node.wtype, cell.rank, cell.mb)]
    if len(paired) != 1 or paired[0][0] >= source_index:
        raise ValueError('bw-linear original forward mirror missing/ambiguous/out of order')
    fw_index, fw = paired[0]
    if fw.opname.name != 'FW_linear':
        raise ValueError('bw-linear original forward opcode mismatch')
    if cell.ir.mirror.signature != 'torch.nn.functional.linear':
        raise ValueError('bw-linear original forward function signature mismatch')
    if (len(cell.inputs) != 3 or len(cell.outputs) != 2
            or len(fw.inputs) != 2 or len(fw.outputs) != 1
            or len(cell._input_irs) != 3 or len(cell._output_irs) != 2):
        raise ValueError('bw-linear complete original ordered ports required')
    for kwargs in (cell.kwargs, fw.kwargs):
        if (set(kwargs) - {'bias', '__consts'} or kwargs.get('bias') is not None
                or kwargs.get('__consts', []) != []):
            raise ValueError('bw-linear unsupported bias/kwargs')
    from Verdict.runtime_lineage import _same_typed
    for original, name in ((cell, 'BW.' + cell.ir.mirror.name), (fw, cell.ir.mirror.name)):
        if not _same_typed(tuple(original.node),
                           (original.wtype.value, original.rank, original.mb, original.ir.cid, name)):
            raise ValueError('bw-linear original typed node/IR identity mismatch')
    if not _same_typed([tuple(r) for r in cell.inputs[1:]], [tuple(r) for r in fw.inputs]):
        raise ValueError('bw-linear saved primal fullref/version identity mismatch')
    for refs, irs in ((cell.inputs, cell._input_irs), (cell.outputs, cell._output_irs)):
        for ref, ir in zip(refs, irs, strict=True):
            expected = (cell.node.wtype, cell.rank, -1 if ir.is_attr() else cell.mb, ir.tid)
            if (not _same_typed(tuple(ref)[:4], expected) or type(ref.v) is not int or ref.v < 0):
                raise ValueError('bw-linear ordered source fullref/IR identity mismatch')
    g, x, w = cell._input_irs
    originals = list(cell.ir.inputs()) + list(cell.ir.mirror.inputs())
    original_outputs = list(cell.ir.outputs())
    forward_inputs, forward_outputs = list(cell.ir.mirror.inputs()), list(cell.ir.mirror.outputs())
    if (len(forward_inputs) != 2 or len(forward_outputs) != 1
            or len(originals) != 3 or len(original_outputs) != 2):
        raise ValueError('bw-linear original mirror arity mismatch')
    for actual, expected in ((cell._input_irs, originals),
                             (cell._output_irs, original_outputs),
                             (fw._input_irs, forward_inputs),
                             (fw._output_irs, forward_outputs),
                             ([g], [forward_outputs[0].grad]),
                             (cell._output_irs, [t.grad for t in forward_inputs])):
        if not _same_typed([_ir_identity(t) for t in actual], [_ir_identity(t) for t in expected]):
            raise ValueError('bw-linear original mirror saved/gradient metadata identity mismatch')
    # Fullref versions are source reads, not merely same-shaped tid aliases.
    for ref, ir in zip(cell.inputs, cell._input_irs, strict=True):
        if ref.v == 0 and not (ir.is_attr() is True and ir.is_grad() is False):
            raise ValueError('bw-linear external activation/cotangent identity lacks source writer authority')
        writers = [(i, c) for i, c in enumerate(cells[:source_index])
                   if any(_same_typed(tuple(r), tuple(ref)) for r in c.outputs)]
        if ref.v != 0 and len(writers) != 1:
            raise ValueError('bw-linear input source writer/version identity missing/ambiguous')
    watched = [tuple(r) for r in (*cell.inputs, *cell.outputs)]
    for later in cells[source_index+1:]:
        if any(_same_typed(tuple(r), key) for r in later.outputs for key in watched):
            raise ValueError('bw-linear input/output fullref suffix overwrite')
    if len(x.shape) not in (2, 3) or len(w.shape) != 2 or x.shape[-1] != w.shape[1] or tuple(g.shape) != (*x.shape[:-1], w.shape[0]):
        raise ValueError('bw-linear contraction/shape mismatch')
    return dict(bw_node=list(cell.node), fw_node=list(fw.node),
                source_index=source_index, fw_source_index=fw_index,
                inputs=[list(r) for r in cell.inputs], outputs=[list(r) for r in cell.outputs],
                saved_inputs=[list(r) for r in fw.inputs],
                input_roles=['cotangent', 'saved_input', 'saved_weight'], output_roles=['dx', 'dw'],
                weight_layout='out_features,in_features', reduction_axes=list(range(len(x.shape)-1)),
                scale='supplied-cotangent; no additional local scaling',
                obligations=['cotangent provenance and loss/accumulation scaling',
                             'forward saved-input value reconstruction',
                             'parameter value/layout reconstruction',
                             'DP contribution ownership and WRED scaling'],
                proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
