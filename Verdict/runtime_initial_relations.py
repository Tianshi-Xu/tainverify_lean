"""Bind runtime parameter evidence to ORIGINAL typed initial relations.

Caller: graph_to_lean._generate, after runtime_input_feed.bind. Pass the fresh
seed_input['parameter_inputs'], original trace lineages and live validation.
This is a structural compiler binding, NOT authentication of tensor values:
load_bundle/validate_parameters must have checked the current observations.
No saved JSON receipt substitutes for the independently retained trace inputs.
"""
from copy import deepcopy
from dataclasses import asdict

import re

from Verdict.runtime_lineage import Role, _Index, _TraceValidation, _same_typed, op, trace


def _authenticate(sm, pm, parameters, lineages, validation):
    if type(validation) is not _TraceValidation:
        raise ValueError('missing independent initial relation trace authority')
    canonical, _, current = trace(sm, pm, *validation._inputs)
    if not _same_typed(dict(validation), dict(current)) or not _same_typed(lineages, canonical):
        raise ValueError('initial targets differ from current original raw/batch authority')
    raw_sm, raw_pm, _, batch, receipt, _ = validation._inputs
    plan = receipt['compute']['plan_ngpus']; runtime = receipt['compute']['runtime_ngpus']
    size = receipt['batch_size']
    expected_units = [dict(unit=u, ranks=list(range(u*plan, (u+1)*plan)),
                           positions=list(range(u*size, (u+1)*size))) for u in range(runtime//plan)]
    if (not _same_typed(batch['config']['units'], expected_units)
            or not _same_typed((pm.W.plan_ndevs, pm.W.runtime_ndevs), (plan, runtime))
            or not _same_typed(sm.W.runtime_ndevs, 1)):
        raise ValueError('current view/DP-unit topology mismatch')
    if (parameters.get('status') != 'current-run-parameter-values-validated'
            or any(parameters.get(flag) is not False for flag in
                   ('proof_admissible', 'kernel_value_proved', 'torch_refinement'))):
        raise ValueError('fresh runtime-only parameter observations required')
    expected = {}; globals_ = {}
    for label, view, raw in [('sm', sm, raw_sm), ('pm', pm, raw_pm)]:
        index = _Index(view, raw)
        parents = {}
        for cell in raw:
            if op(cell) not in ('FW_embedding', 'FW_layernorm', 'FW_linear'):
                continue
            for ref, ir in zip(cell.inputs, cell._input_irs, strict=True):
                if not ir.is_param():
                    continue
                ref = tuple(ref)
                if ref[1] != cell.rank or (ref in parents and parents[ref] != ir.parent.tid):
                    raise ValueError('ambiguous parameter parent/owner')
                parents[ref] = ir.parent.tid
        for ref, meta in index.meta.items():
            if not meta[4] or meta[5] or ref in index.writers:
                continue
            endpoint = index.endpoint(ref, 'initial')
            if ref[0] != label[0] or ref[2] != -1 or ref[4] != 0 or meta[3] != (0, 1):
                raise ValueError('unsupported original parameter fullref/value partition')
            if label == 'sm':
                if meta[0] in globals_ or meta[2] != tuple((0, d) for d in meta[1]):
                    raise ValueError('ambiguous/sliced global parameter identity')
                globals_[meta[0]] = ref
            if meta[0] not in globals_:
                raise ValueError('missing original global parameter identity')
            expected[ref] = dict(world=label, rank=ref[1], ref=list(ref), tid=endpoint.tid,
                sm_ref=list(globals_[meta[0]]), logical_name=meta[0], parent_tid=parents[ref],
                full_shape=list(meta[1]), bounds=[list(b) for b in meta[2]],
                value_part=list(meta[3]), shape=list(endpoint.shape))
    rows = {}
    for row in parameters['bindings']:
        ref = tuple(row['ref'])
        if ref in rows or ref not in expected:
            raise ValueError('duplicate/absent original parameter binding')
        name = row['runtime_name']
        if not isinstance(name, str) or re.fullmatch(r'.+_' + str(ref[3]), name) is None:
            raise ValueError('runtime parameter source tid mismatch')
        if not _same_typed({k: v for k, v in row.items() if k != 'runtime_name'}, expected[ref]):
            raise ValueError('parameter binding differs from original identity/layout/fullref')
        rows[ref] = row
    if rows.keys() != expected.keys():
        raise ValueError('incomplete original parameter binding inventory')
    return rows, canonical


def bind(sm, pm, parameter_inputs, lineages, validation):
    """Return per-DP-unit bindings/goals without generating Lean or admitting proof.

    Only existing typed parameter targets are emitted. Other observed parameters
    are retained as explicit unbound refs, never promoted to inferred relations.
    The result is a receipt, not a reusable authentication token. A replicated
    unit denotes one copy equality per pm_tid (never a gather). Sharded units
    retain canonical rank/slice order and require uniform piece shapes.
    runtime_name is preserved with its source-tid suffix checked; generated
    alias/fullmap authentication and tensor equality remain load_bundle's job.
    """
    try:
        rows, lineages = _authenticate(sm, pm, parameter_inputs, lineages, validation)
    except (KeyError, TypeError, AttributeError, IndexError) as exc:
        raise ValueError(f'malformed initial parameter relation authority: {exc}') from exc
    relations = []; covered = set()
    for lineage in lineages:
        if lineage.role != Role.PARAMETER:
            continue
        sm_binding = rows[lineage.target.ref]
        covered.add(lineage.target.ref)
        units = []
        for unit in lineage.units:
            bindings = [rows[p.endpoint.ref] for p in unit.pieces]
            covered.update(p.endpoint.ref for p in unit.pieces)
            if any(p.endpoint.shape != unit.pieces[0].endpoint.shape for p in unit.pieces):
                raise ValueError('typed parameter goal requires uniform shard shapes')
            copied = unit.reconstruction == 'tp-copy-obligation'
            dim = None if copied else int(unit.reconstruction.split(':')[1])
            goal = dict(kind='replicated' if copied else 'sharded', sm_tid=lineage.target.tid,
                        pm_tids=[p.endpoint.tid for p in unit.pieces], dim=dim,
                        sm_shape=list(lineage.target.shape), pm_shape=list(unit.pieces[0].endpoint.shape))
            units.append(dict(unit=unit.unit, bindings=deepcopy(bindings), initial_goal=goal))
        relations.append(dict(lineage=asdict(lineage), sm_binding=deepcopy(sm_binding), units=units))
    return dict(status='initial-parameter-relations-bound', relations=relations,
                unbound_parameter_refs=[list(ref) for ref in rows if ref not in covered],
                unproved_value_obligations=['initial-parameter-value-equality-unproved'],
                proof_admissible=False, public_complete=False,
                kernel_value_proved=False, torch_refinement=False)


def attach(world, sm, pm, parameter_inputs, lineages, validation):
    """Append source-derived conditional initial contracts to the same entry.

    Explicit shape/slice/value equations are caller premises. Runtime evidence
    never becomes a proof of those premises, nor of whole-model equivalence.
    """
    from Verdict.runtime_world import WorldDefinitions, _proof_bundle
    bound = bind(sm, pm, parameter_inputs, lineages, validation)
    goals = [u['initial_goal'] for row in bound['relations'] for u in row['units']]
    result = dict(world.receipt)
    result['initial_relations'] = dict(bound, contract_emitted=bool(goals))
    if not goals:
        return WorldDefinitions(world.lean, result, world.supporting_sources)
    specs = []
    for goal in goals:
        ts = goal['sm_tid']; tids = goal['pm_tids']; shape = goal['sm_shape']
        if goal['kind'] == 'replicated':
            specs.append(f'.replicated {ts} {tids} {shape}')
        else:
            specs.append(f".sharded {ts} {tids} {goal['dim']} {shape} {goal['pm_shape']}")
    text = '\n'.join([
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'open SourceInitialParameterSpecs', 'set_option maxHeartbeats 500000',
        'private def initialParameterSpecs : List Spec := [',
        ',\n'.join(specs) + ']',
        'private theorem initialParameterSpecs_valid : All Spec.valid initialParameterSpecs := by decide',
        'def InitialParameterValues (initSM initPM : Store) : Prop :=',
        '  All (fun spec => spec.values initSM initPM) initialParameterSpecs',
        'def InitialParameterRelations (initSM initPM : Store) : Prop :=',
        '  All (fun spec => spec.fact.Holds initSM initPM) initialParameterSpecs',
        'theorem initialParameterRelations_of_values (initSM initPM : Store)',
        '    (h : InitialParameterValues initSM initPM) : InitialParameterRelations initSM initPM :=',
        '  all_of_values initialParameterSpecs initSM initPM initialParameterSpecs_valid h',
        '#print axioms initialParameterRelations_of_values',
        'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    marker = 'import denote.SourceScopedPrefix\n'
    if world.lean.count(marker) != 1:
        raise ValueError('initial relation attachment requires canonical prefix entry')
    entry = world.lean.replace(marker, marker + 'import denote.SourceInitialParameterSpecs\n', 1) + '\n' + text
    if 'input_feed' in world.receipt:
        from Verdict.runtime_input_relations import render as render_input_relations
        input_text, input_detail = render_input_relations(
            world.receipt['input_feed'], lineages, world.receipt['execution_order'])
        entry = entry.replace('import denote.SourceInitialParameterSpecs\n',
            'import denote.SourceInitialParameterSpecs\nimport denote.SourceInitialInputEncoding\nimport denote.SourceInitialInputRead\n', 1)
        entry += '\n' + input_text
        result['input_relations'] = input_detail
        from Verdict.runtime_embedding_values import render as render_embedding_values
        embedding_text, embedding_detail = render_embedding_values(
            sm, pm, lineages, world.receipt['execution_order'])
        if embedding_detail['reads']:
            entry = entry.replace('import denote.SourceInitialInputRead\n',
                                  'import denote.SourceEmbeddingRead\n', 1)
            entry += '\n' + embedding_text
        result['embedding_values'] = embedding_detail
        entry = entry.replace('import denote.SourceInitialParameterSpecs\n',
                              'import denote.SourceParameterFrame\n', 1)
        entry += '\n' + '\n'.join([
            'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
            'set_option maxHeartbeats 500000',
            'private theorem parameterUnwritten : SourceInitialParameterSpecs.All',
            '    (fun spec => SourceParameterFrame.SpecUnwritten spec',
            '      (smInputRequests.flatMap (fun r => r.1.outs))',
            '      (pmInputRequests.flatMap (fun r => r.1.outs))) initialParameterSpecs := by decide',
            'theorem initialParameterValues_final (s p t q : Store)',
            '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
            '    (h : InitialParameterValues s p) : InitialParameterValues t q :=',
            '  SourceParameterFrame.all_values_runWithInputs initialParameterSpecs smGraph pmGraph',
            '    smScope pmScope smPeers pmPeers smGraph.nodes pmGraph.nodes smInputRequests pmInputRequests',
            '    s p t q parameterUnwritten hs hp h',
            '#print axioms initialParameterValues_final',
            'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
        result['initial_relations']['frame_emitted'] = True
        from Verdict.runtime_embedding_units import render as render_embedding_units
        unit_text, unit_detail = render_embedding_units(sm, pm, lineages, bound)
        if unit_detail['units']:
            entry = entry.replace('import denote.SourceEmbeddingRead\n',
                                  'import denote.SourceEmbeddingRead\nimport denote.SourceEmbeddingUnit\n', 1)
            entry += '\n' + unit_text
            from Verdict.runtime_relation_source import compact
            prefix, boundary, suffix = entry.partition(text)
            assert boundary
            entry = prefix + compact(text + suffix)
        result['embedding_units'] = unit_detail
        from Verdict.runtime_embedding_route_values import render as render_route_values
        route_text, route_detail = render_route_values(
            sm, pm, lineages, validation, world.receipt['execution_order'])
        if route_detail['reads']:
            entry = entry.replace('import denote.SourceInitialInputRead\n',
                                  'import denote.SourceEmbeddingRead\n', 1)
            entry = entry.replace('import denote.SourceEmbeddingRead\n',
                                  'import denote.SourceEmbeddingRead\nimport denote.SourcePrimitiveRead\n', 1)
            entry += '\n' + route_text
        result['embedding_route_values'] = route_detail
        if route_detail['routes']:
            from Verdict.runtime_embedding_position_units import render as render_position_units
            position_text, position_detail = render_position_units(sm, pm, lineages, validation, bound)
            if position_detail['units']:
                entry = entry.replace('import denote.SourcePrimitiveRead\n',
                    'import denote.SourcePrimitiveRead\nimport denote.SourceEmbeddingPositionUnit\n', 1)
                entry += '\n' + position_text
            result['embedding_position_units'] = position_detail
        from Verdict.runtime_add_values import render as render_add_values
        add_text, add_detail = render_add_values(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if add_detail['units']:
            entry = entry.replace('import denote.SourceEmbeddingRead\n',
                'import denote.SourceEmbeddingRead\nimport denote.SourceAddRead\nimport denote.SourceAddUnit\n', 1)
            entry += '\n' + add_text
        result['add_values'] = add_detail
    result['proof_bundle'] = _proof_bundle(entry, world.supporting_sources)
    return WorldDefinitions(entry, result, world.supporting_sources)
