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
                'import denote.SourceEmbeddingRead\nimport denote.SourceAddRead\nimport denote.SourceAddUnit\nimport denote.SourceAddFacts\n', 1)
            entry += '\n' + add_text
        result['add_values'] = add_detail
        from Verdict.runtime_post_add_values import render as render_post_add
        post_text, post_detail = render_post_add(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if post_detail['reads']:
            entry = entry.replace('import denote.SourceAddFacts\n',
                'import denote.SourceAddFacts\nimport denote.SourceMultirefRead\nimport denote.SourceHiddenSequenceExchange\n', 1)
            entry += '\n' + post_text
        result['post_add_values'] = post_detail
        from Verdict.runtime_layernorm_values import render as render_layernorm
        layernorm_text, layernorm_detail = render_layernorm(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if layernorm_detail['reads']:
            entry = entry.replace('import denote.SourceHiddenSequenceExchange\n',
                'import denote.SourceHiddenSequenceExchange\nimport denote.SourceLayernormRead\nimport denote.SourceLayernormUnit\n', 1)
            entry += '\n' + layernorm_text
        result['layernorm_values'] = layernorm_detail
        from Verdict.runtime_projection_values import render as render_projections
        projection_text, projection_detail = render_projections(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if projection_detail['reads']:
            entry = entry.replace('import denote.SourceLayernormUnit\n',
                'import denote.SourceLayernormUnit\nimport denote.SourceLinearRead\nimport denote.SourceAllGatherRead\nimport denote.SourceLinearUnit\n', 1)
            entry += '\n' + projection_text
        result['projection_values'] = projection_detail
        from Verdict.runtime_view_values import render as render_views
        view_text, view_detail = render_views(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if view_detail['reads']:
            entry = entry.replace('import denote.SourceLinearUnit\n',
                'import denote.SourceLinearUnit\nimport denote.SourceLayoutRead\nimport denote.SourceViewUnit\n', 1)
            entry += '\n' + view_text
        result['view_values'] = view_detail
        from Verdict.runtime_projection_exchange_values import render as render_projection_exchanges
        exchange_text, exchange_detail = render_projection_exchanges(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if exchange_detail['reads']:
            entry = entry.replace('import denote.SourceViewUnit\n',
                'import denote.SourceViewUnit\nimport denote.SourceRank4Exchange\n', 1)
            entry += '\n' + exchange_text
        result['projection_exchange_values'] = exchange_detail
        from Verdict.runtime_transpose_values import render as render_transposes
        transpose_text, transpose_detail = render_transposes(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if transpose_detail['reads']:
            entry = entry.replace('import denote.SourceRank4Exchange\n',
                'import denote.SourceRank4Exchange\nimport denote.SourceTransposeUnit\n', 1)
            entry += '\n' + transpose_text
        result['transpose_values'] = transpose_detail
        from Verdict.runtime_post_transpose_values import render as render_post_transposes
        post_text, post_detail = render_post_transposes(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if post_detail['reads']:
            entry = entry.replace('import denote.SourceTransposeUnit\n',
                'import denote.SourceTransposeUnit\nimport denote.SourceTranspose23Unit\nimport denote.SourceRank4ReverseExchange\n', 1)
            entry += '\n' + post_text
        result['post_transpose_values'] = post_detail
        from Verdict.runtime_middle_exchange_values import render as render_middle_exchanges
        middle_text, middle_detail = render_middle_exchanges(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if middle_detail['reads']:
            entry = entry.replace('import denote.SourceRank4ReverseExchange\n',
                'import denote.SourceRank4ReverseExchange\nimport denote.SourceRank4MiddleExchange\n', 1)
            entry += '\n' + middle_text
        result['middle_exchange_values'] = middle_detail
        from Verdict.runtime_matmul_values import render as render_matmuls
        matmul_text, matmul_detail = render_matmuls(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if matmul_detail['reads']:
            entry = entry.replace('import denote.SourceRank4MiddleExchange\n',
                'import denote.SourceRank4MiddleExchange\nimport denote.SourceMatmulRead\nimport denote.SourceMatmulUnit\n', 1)
            entry += '\n' + matmul_text
        result['matmul_values'] = matmul_detail
        from Verdict.runtime_matmul_exchange_values import render as render_matmul_exchanges
        matmul_exchange_text, matmul_exchange_detail = render_matmul_exchanges(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if matmul_exchange_detail['reads']:
            entry += '\n' + matmul_exchange_text
        result['matmul_exchange_values'] = matmul_exchange_detail
        from Verdict.runtime_div_values import render as render_divs
        div_text, div_detail = render_divs(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if div_detail['reads']:
            entry = entry.replace('import denote.SourceMatmulUnit\n',
                'import denote.SourceMatmulUnit\nimport denote.SourceDivRead\nimport denote.SourceDivUnit\n', 1)
            entry += '\n' + div_text
        result['div_values'] = div_detail
        from Verdict.runtime_div_exchange_values import render as render_div_exchanges
        div_exchange_text, div_exchange_detail = render_div_exchanges(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if div_exchange_detail['reads']:
            entry += '\n' + div_exchange_text
        result['div_exchange_values'] = div_exchange_detail
        from Verdict.runtime_softmax_values import render as render_softmaxes
        softmax_text, softmax_detail = render_softmaxes(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if softmax_detail['reads']:
            entry = entry.replace('import denote.SourceDivUnit\n',
                'import denote.SourceDivUnit\nimport denote.SourceSoftmaxRead\nimport denote.SourceSoftmaxUnit\n', 1)
            entry += '\n' + softmax_text
        result['softmax_values'] = softmax_detail
        from Verdict.runtime_softmax_exchange_values import render as render_softmax_exchanges
        softmax_exchange_text, softmax_exchange_detail = render_softmax_exchanges(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if softmax_exchange_detail['reads']:
            entry = entry.replace('import denote.SourceSoftmaxUnit\n',
                'import denote.SourceSoftmaxUnit\nimport denote.SourceRank4InnerExchange\n', 1)
            entry += '\n' + softmax_exchange_text
        result['softmax_exchange_values'] = softmax_exchange_detail
        from Verdict.runtime_query_matmul_values import render as render_query_matmuls
        query_matmul_text, query_matmul_detail = render_query_matmuls(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if query_matmul_detail['reads']:
            entry = entry.replace('import denote.SourceRank4InnerExchange\n',
                'import denote.SourceRank4InnerExchange\nimport denote.SourceQueryMatmulUnit\n', 1)
            entry += '\n' + query_matmul_text
        result['query_matmul_values'] = query_matmul_detail
        from Verdict.runtime_query_transpose_values import render as render_query_transposes
        query_transpose_text, query_transpose_detail = render_query_transposes(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if query_transpose_detail['reads']:
            entry = entry.replace('import denote.SourceQueryMatmulUnit\n',
                'import denote.SourceQueryMatmulUnit\nimport denote.SourceQueryTransposeUnit\n', 1)
            entry += '\n' + query_transpose_text
        result['query_transpose_values'] = query_transpose_detail
        from Verdict.runtime_contiguous_values import render as render_contiguous
        contiguous_text, contiguous_detail = render_contiguous(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if contiguous_detail['reads']:
            entry = entry.replace('import denote.SourceQueryTransposeUnit\n',
                'import denote.SourceQueryTransposeUnit\nimport denote.SourceContiguousRead\n', 1)
            entry += '\n' + contiguous_text
        result['contiguous_values'] = contiguous_detail
        from Verdict.runtime_contiguous_exchange_values import render as render_contiguous_exchange
        contiguous_exchange_text, contiguous_exchange_detail = render_contiguous_exchange(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if contiguous_exchange_detail['reads']:
            entry += '\n' + contiguous_exchange_text
        result['contiguous_exchange_values'] = contiguous_exchange_detail
        from Verdict.runtime_view_flatten_values import render as render_view_flatten
        view_flatten_text, view_flatten_detail = render_view_flatten(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if view_flatten_detail['reads']:
            entry = entry.replace('import denote.SourceContiguousRead\n',
                'import denote.SourceContiguousRead\nimport denote.SourceViewFlattenUnit\n', 1)
            entry += '\n' + view_flatten_text
        result['view_flatten_values'] = view_flatten_detail
        from Verdict.runtime_view_flatten_exchange_values import render as render_view_flatten_exchange
        view_flatten_exchange_text, view_flatten_exchange_detail = render_view_flatten_exchange(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if view_flatten_exchange_detail['reads']:
            entry += '\n' + view_flatten_exchange_text
        result['view_flatten_exchange_values'] = view_flatten_exchange_detail
        from Verdict.runtime_output_projection_values import render as render_output_projection
        output_projection_text, output_projection_detail = render_output_projection(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if output_projection_detail['reads']:
            entry += '\n' + output_projection_text
        result['output_projection_values'] = output_projection_detail
        from Verdict.runtime_output_projection_exchange_values import render as render_output_projection_exchange
        output_exchange_text, output_exchange_detail = render_output_projection_exchange(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if output_exchange_detail['reads']:
            entry = entry.replace('import denote.SourceViewFlattenUnit\n',
                'import denote.SourceViewFlattenUnit\nimport denote.SourceSequenceHiddenExchange\n', 1)
            entry += '\n' + output_exchange_text
        result['output_projection_exchange_values'] = output_exchange_detail
        from Verdict.runtime_attention_residual_values import render as render_attention_residual
        residual_text, residual_detail = render_attention_residual(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if residual_detail['reads']:
            entry += '\n' + residual_text
        result['attention_residual_values'] = residual_detail
        from Verdict.runtime_frontier_alias_exchange_values import render as render_frontier_alias_exchange
        frontier_text, frontier_detail = render_frontier_alias_exchange(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if frontier_detail['reads']:
            entry += '\n' + frontier_text
        result['frontier_alias_exchange_values'] = frontier_detail
        from Verdict.runtime_frontier_layernorm_values import render as render_frontier_layernorm
        frontier_ln_text, frontier_ln_detail = render_frontier_layernorm(
            sm, pm, lineages, validation, bound, world.receipt['execution_order'])
        if frontier_ln_detail['reads']:
            entry += '\n' + frontier_ln_text
        result['frontier_layernorm_values'] = frontier_ln_detail
        if unit_detail['units'] or result.get('embedding_position_units', {}).get('units'):
            entry = entry.replace('import denote.SourceEmbeddingRead\n',
                'import denote.SourceEmbeddingRead\nimport denote.SourceEmbeddingFacts\n', 1)
    from Verdict.runtime_binder_source import compact as compact_binders
    from Verdict.runtime_read_source import compact as compact_reads
    entry = compact_reads(compact_binders(entry))
    result['proof_bundle'] = _proof_bundle(entry, world.supporting_sources)
    return WorldDefinitions(entry, result, world.supporting_sources)
