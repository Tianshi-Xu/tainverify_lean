"""Compile authenticated ordered feed slices into Tensor-value equalities.

The caller supplies fresh runtime_input_feed output and independently retraced
lineages. Python checks bind endpoints; Lean checks the emitted list equations.
"""
from Verdict.runtime_lineage import Role, _same_typed


def render(feed, lineages):
    if feed.get('source_validated') is not True:
        raise ValueError('fresh source-validated feeds required')
    ports = {}
    for loader in feed['loaders']:
        for port in loader['ports']:
            tid = port['tid']
            if tid in ports:
                raise ValueError('duplicate input feed port')
            ports[tid] = (loader, port)
    used = set(); slices = []; proofs = []
    fields = ('world', 'runtime_rank', 'microbatch', 'source_tid', 'version')

    def endpoint(e):
        if e.tid not in ports:
            raise ValueError('missing original input feed port')
        loader, p = ports[e.tid]
        ref = tuple(p['ref'][f] for f in fields)
        if (not _same_typed(ref, e.ref) or not _same_typed(tuple(loader['node']), e.writer)
                or not _same_typed(p['shape'], list(e.shape))
                or len(e.shape) != 2 or any(type(v) is not int for v in p['values'])
                or len(p['values']) != e.shape[0]*e.shape[1]):
            raise ValueError('input feed identity/shape/encoding mismatch')
        used.add(e.tid)
        return p, f"{loader['world']}Node_{loader['index']}_port{p['port']}"

    for lineage in lineages:
        if lineage.role != Role.BATCH:
            continue
        full, full_name = endpoint(lineage.target)
        units = len(lineage.units)
        if not units or full['shape'][1] <= 0:
            raise ValueError('unsupported empty input units/width')
        width = full['shape'][1]
        for unit_index, unit in enumerate(lineage.units):
            rows = len(unit.positions)
            if (rows <= 0 or full['shape'][0] != rows*units
                    or unit.unit != unit_index
                    or tuple(unit.positions) != tuple(range(unit_index*rows,(unit_index+1)*rows))
                    or unit.reconstruction != 'tp-copy-obligation' or not unit.pieces):
                raise ValueError('unsupported ordered input batch decomposition')
            for piece in unit.pieces:
                local, local_name = endpoint(piece.endpoint)
                start = unit_index*rows*width
                if (local['shape'] != [rows,width] or
                        not _same_typed(local['values'],full['values'][start:start+rows*width])):
                    raise ValueError('input values differ from ordered original batch slice')
                name = f'inputSlice_{lineage.target.tid}_{piece.endpoint.tid}'
                proofs += [f'theorem {name} : {local_name} = chunkPrimDimN 0 {units} {unit_index} {full_name} :=',
                    f'  SourceInitialInputEncoding.emitted_ordered_slice_eq_chunk {full_name} {local_name}',
                    f'    {full_name}_values {local_name}_values {units} {unit_index} {rows} {width}',
                    '    rfl rfl (by decide) (by decide) (by decide) rfl rfl (by decide)',
                    f'#print axioms {name}']
                slices.append(dict(theorem=name,sm_ref=list(lineage.target.ref),pm_ref=list(piece.endpoint.ref),
                                   unit=unit_index,rows=rows,width=width))
    if used != set(ports):
        raise ValueError('incomplete typed input feed coverage')
    text = '\n'.join(['namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs,'end','end TrainVerify.Denote.RuntimeWorld',''])
    return text, dict(status='ordered-input-slice-equalities-emitted',slices=slices,
                      kernel_value_proved=False,proof_admissible=False,torch_refinement=False)
