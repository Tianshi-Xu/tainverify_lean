"""Original multiref adjoint: ordered cotangents -> tensorSum, never an alias.

Raw IR mirror/grad metadata is authority; prepared fullrefs supply source
versions and runtime ownership. This local boundary does not close any AA or
cross-model value relation, scaling, or torch refinement.
"""
from trainverify.backward_linear_authority import _ir_identity
from Verdict.runtime_lineage import _same_typed


def _require(ok, message):
    if not ok:
        raise ValueError('bw-multiref ' + message)


def _identities(tensors):
    try:
        return [_ir_identity(t) for t in tensors]
    except (ValueError, AttributeError, TypeError) as exc:
        raise ValueError('bw-multiref original gradient metadata required') from exc


def bind(cells, source_index):
    """Fresh original raw BW ports, FW output.grad order, and source writers."""
    from nnscaler.ir.operator import IRBpOperation, IRFwOperation
    _require(type(source_index) is int and 0 <= source_index < len(cells), 'invalid source index')
    cell = cells[source_index]
    _require(isinstance(cell.ir, IRBpOperation) and cell.opname.name == 'BW_multiref',
             'original typed backward operation required')
    mirror = cell.ir.mirror
    _require(isinstance(mirror, IRFwOperation) and mirror.mirror is cell.ir,
             'original reciprocal forward mirror required')
    paired = [(i, c) for i, c in enumerate(cells) if c.ir is mirror and
              _same_typed(tuple(c.node[:3]), tuple(cell.node[:3]))]
    _require(len(paired) == 1 and paired[0][0] < source_index, 'forward mirror missing/ambiguous/order')
    fw_index, fw = paired[0]
    _require(fw.opname.name == 'FW_multiref' and mirror.signature == 'nnscaler.runtime.function.multiref'
             and cell.ir.signature == 'torch.autograd.grad', 'original mirror signature/opcode mismatch')
    times = mirror.kwargs.get('times')
    _require(type(times) is int and times > 0, 'original mirror times required')
    _require(set(mirror.kwargs) <= {'times', '__consts'} and
             _same_typed(mirror.kwargs.get('__consts', []), []) and
             set(cell.ir.kwargs) <= {'__consts'} and
             _same_typed(cell.ir.kwargs.get('__consts', []), []), 'original kwargs mismatch')
    raw_fi, raw_fo = list(mirror.inputs()), list(mirror.outputs())
    raw_bi, raw_bo = list(cell.ir.inputs()), list(cell.ir.outputs())
    _require(len(raw_fi) == len(raw_bo) == 1 and len(raw_fo) == len(raw_bi) == times,
             'complete original ordered gradient ports/times mismatch')
    _require(_same_typed(_identities(raw_bi), _identities([t.grad for t in raw_fo])) and
             _same_typed(_identities(raw_bo), _identities([t.grad for t in raw_fi])),
             'original ordered gradient metadata mismatch')
    for original, index, raw_inputs, raw_outputs, name in (
        (cell, source_index, raw_bi, raw_bo, 'BW.' + mirror.name),
        (fw, fw_index, raw_fi, raw_fo, mirror.name)):
        _require(_same_typed(tuple(original.node),
                 (original.wtype.value, original.rank, original.mb, original.ir.cid, name)),
                 'original node/cid/owner identity mismatch')
        _require(_same_typed(original.kwargs, original.ir.kwargs), 'translated source kwargs mismatch')
        for side, raw in (('inputs', raw_inputs), ('outputs', raw_outputs)):
            refs, irs = getattr(original, side), getattr(original, '_' + side[:-1] + '_irs')
            _require(len(refs) == len(raw) and _same_typed(_identities(irs), _identities(raw)),
                     'translated ordered original ports mismatch')
            for ref, ir in zip(refs, raw, strict=True):
                key = (original.node.wtype, original.rank, -1 if ir.is_attr() else original.mb, ir.tid)
                _require(_same_typed(tuple(ref[:4]), key) and type(ref.v) is int and ref.v >= 0,
                         'complete fullref/IR identity mismatch')
                prior = [(j, c, port) for j, c in enumerate(cells[:index])
                         for port, r in enumerate(c.outputs) if _same_typed(tuple(r[:4]), key)]
                _require(ref.v == len(prior) + (side == 'outputs'), 'source fullref version mismatch')
                if side == 'inputs':
                    exact = [(j, c, port) for j, c, port in prior
                             if _same_typed(tuple(c.outputs[port]), tuple(ref))]
                    _require(len(exact) == 1 or (not prior and ref.v == 0 and ir.is_attr() and not ir.is_grad()),
                             'input source writer/version missing/ambiguous')
                    if exact:
                        _, writer, port = exact[0]
                        _require(_same_typed(_identities([writer._output_irs[port]]), _identities([ir])),
                                 'source writer original tensor metadata mismatch')
    watched = [tuple(r) for r in (*cell.inputs, *cell.outputs)]
    _require(not any(_same_typed(tuple(r), key) for later in cells[source_index+1:]
                     for r in later.outputs for key in watched), 'input/output fullref suffix overwrite')
    _require(all(t.is_grad() is True and _same_typed(tuple(t.shape), tuple(raw_bo[0].shape))
                 for t in raw_bi + raw_bo), 'gradient sum shape/role mismatch')
    contributions = []
    for port, ref in enumerate(cell.inputs):
        writers = [(j, c) for j, c in enumerate(cells[:source_index])
                   if any(_same_typed(tuple(r), tuple(ref)) for r in c.outputs)]
        _require(len(writers) == 1, 'contribution writer missing/ambiguous')
        j, writer = writers[0]
        contributions.append(dict(port=port, ref=list(ref), source_index=j, node=list(writer.node),
            op=writer.opname.name, value_relation_closed=False,
            obligation=('AA value relation remains open; do not identify its input with this contribution'
                        if writer.opname.name in ('AllToAllPrim', 'AllToAllAllToAllPrim')
                        else 'upstream cotangent value relation and scaling remain open')))
    return dict(source_index=source_index, fw_source_index=fw_index,
        bw_node=list(cell.node), fw_node=list(fw.node), times=times,
        inputs=[list(r) for r in cell.inputs], outputs=[list(r) for r in cell.outputs],
        saved_inputs=[], input_roles=['cotangent'] * times, output_roles=['summed_cotangent'],
        semantics='tensorSum; ordered gradient contributions', contributions=contributions,
        obligations=['all ordered upstream contribution value relations', 'loss/accumulation scaling'],
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
