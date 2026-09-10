"""One source-connected hidden embedding value theorem per DP unit.

API: render(sm, pm, lineages, bound) -> (lean_text, metadata). Call only after
runtime_initial_relations.bind on the original lowered views, and after emitting
initialParameterValues_final, inputStoreRelation_* and embeddingRead_* in the
same RuntimeWorld namespace. The parent supplies import denote.SourceEmbeddingFacts
and owns aggregate budgeting/builds. No saved receipt authenticates source here.
Generated Lean is UNCOMPILED until the parent kernel-checks the assembled entry.
"""
from dataclasses import asdict

from Verdict.runtime_lineage import Role, _same_typed


def _one(rows, message):
    rows = list(rows)
    if len(rows) != 1:
        raise ValueError(message)
    return rows[0]


def _ports(view, endpoint):
    node = _one((n for n in view.nodes() if tuple(n) == endpoint.writer),
                'embedding original writer not unique')
    if str(view.node_opname(node)).split('.')[-1] != 'FW_embedding':
        return None
    ins, outs = list(view.node_inputs(node)), list(view.node_outputs(node))
    if (len(ins) != 2 or len(outs) != 1 or outs[0].tid != endpoint.tid
            or not _same_typed(tuple(view.source_tensor(outs[0])), endpoint.ref)):
        raise ValueError('embedding original ordered output ports mismatch')
    kw = view.node_kwargs(node)
    weight_shape = tuple(view.tensor_shape(ins[1]))
    if (len(weight_shape) != 2 or type(kw.get('start')) is not int
            or kw['start'] != 0 or kw.get('stop') != weight_shape[0]):
        raise ValueError('unsupported ordinary hidden embedding offset/layout')
    return [(tuple(view.source_tensor(t)), t.tid) for t in ins]


def render(sm, pm, lineages, bound):
    """Join ORIGINAL ordered ports/fullrefs, not lineage indices or equal shapes."""
    if bound.get('status') != 'initial-parameter-relations-bound':
        raise ValueError('canonical initial parameter binding required')
    specs = [(row, unit) for row in bound['relations'] for unit in row['units']]
    proofs, records = [], []
    for activation in lineages:
        if activation.role != Role.ACTIVATION:
            continue
        global_ports = _ports(sm, activation.target)
        if global_ports is None:
            continue
        (ids_ref, sm_ids), (weight_ref, sm_weight) = global_ports
        ids = _one((l for l in lineages if l.role == Role.BATCH
                    and l.target.ref == ids_ref and l.target.tid == sm_ids),
                   'embedding original input lineage missing/ambiguous')
        parameter = _one((l for l in lineages if l.role == Role.PARAMETER
                          and l.target.ref == weight_ref and l.target.tid == sm_weight),
                         'embedding original parameter lineage missing/ambiguous')
        row = _one((r for r in bound['relations']
                    if _same_typed(r['lineage'], asdict(parameter))),
                   'embedding canonical parameter binding mismatch')
        if (not _same_typed(row['sm_binding']['ref'], list(weight_ref))
                or row['sm_binding']['tid'] != sm_weight):
            raise ValueError('embedding original global weight binding mismatch')
        D = len(activation.units)
        if not D or len(ids.units) != D or len(parameter.units) != D:
            raise ValueError('embedding DP unit count mismatch')
        for lineage in (activation, ids, parameter):
            if not _same_typed([x.unit for x in lineage.units], list(range(D))):
                raise ValueError('embedding ordered DP unit identity mismatch')
        for unit in activation.units:
            u = unit.unit
            input_unit = _one((x for x in ids.units if x.unit == u), 'embedding input unit missing')
            weight_unit = _one((x for x in parameter.units if x.unit == u), 'embedding weight unit missing')
            bound_unit = _one((x for x in row['units'] if x['unit'] == u), 'embedding bound unit missing')
            spec_index = next(i for i, (r, x) in enumerate(specs) if r is row and x is bound_unit)
            T = len(unit.pieces)
            if (not T or len(weight_unit.pieces) != T or len(input_unit.pieces) != T
                    or unit.positions != input_unit.positions):
                raise ValueError('embedding DP unit/operand mapping mismatch')
            if (unit.reconstruction != 'tp-axis-gather:2'
                    or weight_unit.reconstruction != 'tp-axis-gather:1'
                    or input_unit.reconstruction != 'tp-copy-obligation'):
                raise ValueError('unsupported non-hidden embedding layout')
            pm_ids, pm_weights, pm_outs, lanes = [], [], [], []
            for piece, wpiece in zip(unit.pieces, weight_unit.pieces, strict=True):
                ports = _ports(pm, piece.endpoint)
                if ports is None:
                    raise ValueError('embedding local producer missing')
                (iref, itid), (wref, wtid) = ports
                lane = _one((j for j, ip in enumerate(input_unit.pieces)
                             if ip.endpoint.ref == iref and ip.endpoint.tid == itid),
                            'embedding original input unit/operand mapping mismatch')
                if (wpiece.endpoint.ref != wref or wpiece.endpoint.tid != wtid
                        or iref[1] != piece.endpoint.ref[1] or wref[1] != iref[1]):
                    raise ValueError('embedding original ordered weight operand mismatch')
                pm_ids.append(itid); pm_weights.append(wtid); pm_outs.append(piece.endpoint.tid); lanes.append(lane)
            goal = bound_unit['initial_goal']
            if (goal['pm_tids'] != pm_weights or goal['sm_tid'] != sm_weight
                    or [b['ref'] for b in bound_unit['bindings']] != [list(p.endpoint.ref) for p in weight_unit.pieces]
                    or [b['tid'] for b in bound_unit['bindings']] != pm_weights):
                raise ValueError('embedding bound ordered weight operand mapping mismatch')
            B, S = input_unit.pieces[0].endpoint.shape
            V, H = weight_unit.pieces[0].endpoint.shape
            fullshape, shardshape = list(parameter.target.shape), [V, H]
            expected_goal = dict(kind='sharded', sm_tid=sm_weight, pm_tids=pm_weights,
                                 dim=1, sm_shape=fullshape, pm_shape=shardshape)
            if not _same_typed(goal, expected_goal):
                raise ValueError('embedding source-derived bound goal mismatch')
            if (any(type(n) is not int or n <= 0 for n in (B, S, V, H))
                    or ids.target.shape != (B*D, S)
                    or parameter.target.shape != (V, H*T)
                    or activation.target.shape != (B*D, S, H*T)
                    or input_unit.positions != tuple(range(u*B, (u+1)*B))):
                raise ValueError('unsupported hidden embedding shape/batch layout')
            for j, (out, weight) in enumerate(zip(unit.pieces, weight_unit.pieces, strict=True)):
                if (out.endpoint.shape != (B, S, H) or weight.endpoint.shape != (V, H)
                        or input_unit.pieces[j].endpoint.shape != (B, S)
                        or weight.bounds != ((0, V), (j*H, (j+1)*H))
                        or out.bounds != ((0, B), (0, S), (j*H, (j+1)*H))
                        or out.value_part != (0, 1) or weight.value_part != (0, 1)):
                    raise ValueError('unsupported ordered hidden embedding shards')
            ws = '[' + ', '.join(f'q {t}' for t in pm_weights) + ']'
            os = '[' + ', '.join(f'q {t}' for t in pm_outs) + ']'
            projection = 'hrels' + '.2' * spec_index + ('.1' if spec_index < len(specs)-1 else '')
            name = f'embeddingUnit_{activation.target.tid}_{u}'
            facts_name = f'embeddingUnitFacts_{activation.target.tid}_{u}'
            proofs += [f'theorem {facts_name} (s p t q : Store)',
                '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
                '    (h : InitialParameterValues s p) :',
                f'    (t {activation.target.tid}).shape = {[B * D, S, H * T]} ∧',
                f'    (∀ x ∈ {os}, x.shape = {[B, S, H]}) ∧',
                f'    chunkPrimDimN 0 {D} {u} (t {activation.target.tid}) =',
                f'    allGatherPrimDimN 2 {T} 0 {os} := by',
                '  have hrels := initialParameterRelations_of_values t q (initialParameterValues_final s p t q hs hp h)',
                f'  have weights : RelationCompiler.ShardedRel (t {sm_weight}) {ws} 1 {fullshape} {shardshape} := {projection}']
            for j, (itid, lane) in enumerate(zip(pm_ids, lanes, strict=True)):
                proofs += [f'  have ids{j} : q {itid} = chunkPrimDimN 0 {D} {u} (t {sm_ids}) :=',
                           f'    (inputStoreRelation_{sm_ids}_{lane} s p t q hs hp).chunk_values {u} (by change {u} < {D}; decide)']
            local = 'List.Forall₂.nil'
            for j in reversed(range(T)):
                equation = f'embeddingRead_{pm_outs[j]} p q hp'
                if j:
                    equation = f'({equation}).trans (congrArg (fun x => fw_embedding x (q {pm_weights[j]})) (ids{j}.trans ids0.symm))'
                local = f'List.Forall₂.cons ({equation}) ({local})'
            proofs += [f'  exact fw_embedding_dp_tp_unit_facts_of_source_eqs {D} {u} {T} {B} {S} {V} {H}',
                f'    (t {sm_ids}) (q {pm_ids[0]}) (t {sm_weight}) {ws} (t {activation.target.tid}) {os}',
                '    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)',
                f'    (inputStoreRelation_{sm_ids}_{lanes[0]} s p t q hs hp).full_shape ids0 rfl',
                f'    weights.shard_shapes weights.full_value (embeddingRead_{activation.target.tid} s t hs)',
                f'    ({local})', f'#print axioms {facts_name}',
                f'theorem {name} (s p t q : Store)',
                '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
                '    (h : InitialParameterValues s p) :',
                f'    chunkPrimDimN 0 {D} {u} (t {activation.target.tid}) =',
                f'    allGatherPrimDimN 2 {T} 0 {os} := by',
                f'  exact ({facts_name} s p t q hs hp h).2.2', f'#print axioms {name}']
            records.append(dict(theorem=name, facts_theorem=facts_name, unit=u, spec_index=spec_index,
                sm_output_ref=list(activation.target.ref), sm_output_tid=activation.target.tid,
                sm_input_ref=list(ids_ref), sm_input_tid=sm_ids, sm_weight_ref=list(weight_ref),
                sm_weight_tid=sm_weight, pm_output_refs=[list(p.endpoint.ref) for p in unit.pieces],
                pm_output_tids=pm_outs, pm_input_tids=pm_ids, pm_weight_tids=pm_weights, input_lanes=lanes,
                pm_input_refs=[list(input_unit.pieces[j].endpoint.ref) for j in lanes],
                pm_weight_refs=[list(p.endpoint.ref) for p in weight_unit.pieces]))
    text = '\n'.join(['namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-embedding-unit-values-emitted-uncompiled', units=records,
        lean_bytes=len(text.encode('utf-8')), kernel_value_proved=False, proof_admissible=False,
        public_complete=False, torch_refinement=False)
