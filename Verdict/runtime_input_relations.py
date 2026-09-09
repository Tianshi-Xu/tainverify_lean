"""Compile authenticated ordered feed slices into Tensor-value equalities.

The caller supplies fresh runtime_input_feed output and independently retraced
lineages. Python checks bind endpoints; Lean checks the emitted list equations.
"""
from Verdict.runtime_lineage import Role, _same_typed


def render(feed, lineages, execution_order=None):
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
    reads = []; relations = []
    if execution_order is not None:
        more, reads, relations = _store_relations(feed, lineages, execution_order)
        proofs += more
    text = '\n'.join(['namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs,'end','end TrainVerify.Denote.RuntimeWorld',''])
    return text, dict(status='ordered-input-slice-equalities-emitted',slices=slices,
                      store_reads=reads,store_relations=relations,
                      kernel_value_proved=False,proof_admissible=False,torch_refinement=False)


def _store_relations(feed, lineages, order):
    """Lift the actual feed values through the original checked world schedules."""
    text = []; reads = []; goals = []; facts = []; calls = []
    for loader in feed['loaders']:
        label = loader['world']; index = loader['index']
        k = order[label]['execution_to_source'].index(index)
        node = f'{label}Node_{index}'; requests = f'{label}InputRequests'
        before = f'({requests}.take {k})'; after = f'({requests}.drop {k+1})'
        split = f'inputSplit_{label}_{index}'
        text += [f'theorem {split} : {requests} = {before} ++ ({node}, some {node}_feed) :: {after} := by',
            '  calc',
            f'    {requests} = {before} ++ {requests}.drop {k} := (List.take_append_drop {k} {requests}).symm',
            '    _ = _ := rfl',f'#print axioms {split}']
        for position,p in enumerate(loader['ports']):
            if p['port'] != position:
                raise ValueError('input port order differs from original feed')
            name = f"inputRead_{p['tid']}"
            member = 'List.mem_cons_self'
            for _ in range(position):member = f'(List.mem_cons_of_mem _ {member})'
            text += [f'theorem {name} (init final : Store) (h : {label}DenoteWithInputs init = some final) :',
                f"    final {p['tid']} = {node}_port{position} :=",
                f'  SourceInitialInputRead.input_value_of_split {label}Graph {label}Scope {label}Peers {label}Graph.nodes',
                f'    {requests} {before} {after} {node} {node}_feed init final',
                f"    {p['tid']} {node}_port{position} {split} rfl {node}_contract {member} h",
                f'#print axioms {name}']
            reads.append(name)
    args = '(smInit pmInit smFinal pmFinal : Store) (hs : smDenoteWithInputs smInit = some smFinal) (hp : pmDenoteWithInputs pmInit = some pmFinal)'
    for lineage in lineages:
        if lineage.role != Role.BATCH:
            continue
        units = len(lineage.units); lanes = len(lineage.units[0].pieces)
        if any(len(u.pieces) != lanes for u in lineage.units):
            raise ValueError('nonuniform TP lanes in input relation')
        ts = lineage.target.tid; fullshape = list(lineage.target.shape)
        for lane in range(lanes):
            pieces = [u.pieces[lane].endpoint for u in lineage.units]
            tids = [p.tid for p in pieces]; shard = list(pieces[0].shape)
            name = f'inputStoreRelation_{ts}_{lane}'
            fact = f'(RelationCompiler.RelationFact.chunked {ts} {tids} 0 {fullshape} {shard}).Holds smFinal pmFinal'
            lhs = '[' + ', '.join(f'pmFinal {tid}' for tid in tids) + ']'
            rhs = '[' + ', '.join(f'chunkPrimDimN 0 {units} {j} (smFinal {ts})' for j in range(units)) + ']'
            rewrites = [f'inputRead_{tid} pmInit pmFinal hp' for tid in tids]+[f'inputRead_{ts} smInit smFinal hs']
            text += [f'theorem {name} {args} : {fact} := by',
                f'  apply SourceInitialParameters.chunked_of_exact_slices smFinal pmFinal {ts} {tids} 0 {units} {fullshape} {shard} (by decide) (by decide)',
                f'  · rw [inputRead_{ts} smInit smFinal hs]; rfl',
                '  · decide',
                f'  · change {lhs} = {rhs}',
                '    rw [' + ', '.join(rewrites) + ']',
                '    rw [' + ', '.join(f'inputSlice_{ts}_{tid}' for tid in tids) + ']',
                f'#print axioms {name}']
            goals.append(name); facts.append(fact); calls.append(f'{name} smInit pmInit smFinal pmFinal hs hp')
    if facts:
        proof = calls[0] if len(calls)==1 else '⟨'+', '.join(calls)+'⟩'
        text += ['def InputStoreRelations (smFinal pmFinal : Store) : Prop :=',
                 '  '+' ∧\n  '.join(facts),
                 f'theorem inputStoreRelations_of_success {args} : InputStoreRelations smFinal pmFinal :=',
                 '  '+proof,'#print axioms inputStoreRelations_of_success']
    return text, reads, goals
