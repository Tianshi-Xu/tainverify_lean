"""Source-connected Chunk/embedding/AA position-unit renderer.

render(sm, pm, lineages, validation, bound) returns a static UNCOMPILED candidate.
The parent owns imports (denote.SourceEmbeddingFacts), source read theorem
emission, integration and kernel checking. A fresh census authenticates original
ports/scopes; neither its DTO nor an old receipt is accepted as source authority.
The bound specification order must be the SAME order used to emit the entry's
initialParameterSpecs; the parent passes one binding to both renderers.
"""
from dataclasses import asdict

from Verdict import runtime_embedding_routes
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import Role, _same_typed


def _list(expressions):
    return '[' + ', '.join(expressions) + ']'


def _cons_equal(equations):
    result = 'rfl'
    for equation in reversed(equations):
        result = f'congrArg₂ List.cons ({equation}) ({result})'
    return result


def _binding(binding, port, sm_ref, world, raw):
    parents = {ir.parent.tid for cell in raw if str(cell.opname).split('.')[-1] == 'FW_embedding'
        for ref, ir in zip(cell.inputs, cell._input_irs, strict=True)
        if _same_typed(tuple(ref), port.endpoint.ref)}
    parent = _one(parents, 'position original parameter parent missing/ambiguous')
    if type(parent) is not int:
        raise ValueError('position original parameter parent identity malformed')
    expected = dict(world=world, rank=port.endpoint.ref[1], ref=list(port.endpoint.ref),
        tid=port.endpoint.tid, sm_ref=list(sm_ref), logical_name=port.parent_name, parent_tid=parent,
        full_shape=list(port.parent_shape), bounds=[list(b) for b in port.bounds],
        value_part=list(port.value_part), shape=list(port.endpoint.shape))
    if not _same_typed({k: binding.get(k) for k in expected}, expected):
        raise ValueError('position embedding original parameter binding identity/shape mismatch')


def render(sm, pm, lineages, validation, bound):
    """Emit only complete complex routes, with all value/shape premises internal."""
    fresh = runtime_embedding_routes.census(sm, pm, lineages, validation)
    if bound.get('status') != 'initial-parameter-relations-bound':
        raise ValueError('canonical initial parameter binding required')
    if fresh.unavailable:
        raise ValueError('unsupported embedding route/layout: ' + '; '.join(x.reason for x in fresh.unavailable))
    try:
        return _render(lineages, bound, fresh, validation._inputs[:2])
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration) as exc:
        raise ValueError(f'malformed position embedding binding/layout: {exc}') from exc


def _render(lineages, bound, fresh, raw):
    specs = [(row, unit) for row in bound['relations'] for unit in row['units']]
    proofs, records = [], []
    for route in fresh.routes:
        if all(r.chunk is None and r.exchange is None for r in route.ranks):
            continue
        if not route.ranks or any(r.chunk is None or r.exchange is None for r in route.ranks):
            raise ValueError('unsupported mixed position embedding route')
        ids = _one((l for l in lineages if l.role == Role.BATCH
            and _same_typed(l.target.ref, route.batch_key)), 'position input lineage missing/ambiguous')
        parameter = _one((l for l in lineages if l.role == Role.PARAMETER
            and _same_typed(l.target.ref, route.parameter_key)), 'position parameter lineage missing/ambiguous')
        row = _one((r for r in bound['relations'] if _same_typed(r['lineage'], asdict(parameter))),
            'position canonical parameter lineage binding mismatch')
        D, T, u = len(ids.units), len(route.ranks), route.unit
        if (type(u) is not int or not 0 <= u < D or len(parameter.units) != D
                or not _same_typed([x.unit for x in ids.units], list(range(D)))
                or not _same_typed([x.unit for x in parameter.units], list(range(D)))
                or not _same_typed(sorted(x['unit'] for x in row['units']), list(range(D)))):
            raise ValueError('position ordered DP unit identity mismatch')
        iu, wu = ids.units[u], parameter.units[u]
        bu = _one((x for x in row['units'] if _same_typed(x['unit'], u)), 'position bound unit missing')
        spec_index = next(i for i, (r, x) in enumerate(specs) if r is row and x is bu)
        if (iu.reconstruction != 'tp-copy-obligation' or wu.reconstruction != 'tp-copy-obligation'
                or len(iu.pieces) != T or len(wu.pieces) != T
                or not _same_typed(iu.positions, route.positions)):
            raise ValueError('unsupported position input/replicated weight unit layout')
        global_ids, global_weight = route.global_embedding.inputs
        global_out, = route.global_embedding.outputs
        if (not _same_typed(global_ids.endpoint, ids.target)
                or not _same_typed(global_weight.endpoint, parameter.target)):
            raise ValueError('position original global operand identity mismatch')
        B, ST = route.ranks[0].loader.endpoint.shape
        V, HT = parameter.target.shape
        if (any(type(n) is not int or n <= 0 for n in (D, T, B, ST, V, HT))
                or ST % T or HT % T):
            raise ValueError('unsupported position positive/divisible shape')
        S, H = ST // T, HT // T
        if (ids.target.shape != (B * D, ST) or global_out.endpoint.shape != (B * D, ST, HT)
                or route.positions != tuple(range(u * B, (u + 1) * B))):
            raise ValueError('unsupported position contiguous batch layout')
        ranks = tuple(r.rank for r in route.ranks)
        pm_loaders, pm_chunks, pm_weights, pm_embeddings, pm_outs, lanes = [], [], [], [], [], []
        for j, rank in enumerate(route.ranks):
            lane = _one((k for k, p in enumerate(iu.pieces)
                if _same_typed(p.endpoint, rank.loader.endpoint)), 'position original loader/unit mismatch')
            weight = rank.embedding.inputs[1]
            chunk, exchange = rank.chunk, rank.exchange
            if (lane != j or not _same_typed(wu.pieces[j].endpoint, weight.endpoint)
                    or rank.loader.endpoint.ref[1] != rank.rank or weight.endpoint.ref[1] != rank.rank
                    or chunk.ranks != ranks or exchange.ranks != ranks
                    or chunk.local_index != j or exchange.local_index != j
                    or chunk.chunk_axis != 1 or exchange.gather_axis != 1 or exchange.split_axis != 2
                    or chunk.inputs != (rank.loader,) or chunk.outputs != (rank.embedding.inputs[0],)
                    or exchange.inputs != tuple(r.embedding.outputs[0] for r in route.ranks)
                    or exchange.peers != tuple((r.rank, r.embedding.outputs[0].endpoint.tid) for r in route.ranks)
                    or exchange.outputs != (rank.output,)):
                raise ValueError('position ordered source unit/peer/operand mapping mismatch')
            expected = [(rank.loader, (B, ST), ((0, B), (0, ST))),
                (rank.embedding.inputs[0], (B, S), ((0, B), (j * S, (j + 1) * S))),
                (weight, (V, HT), ((0, V), (0, HT))),
                (rank.embedding.outputs[0], (B, S, HT), ((0, B), (j * S, (j + 1) * S), (0, HT))),
                (rank.output, (B, ST, H), ((0, B), (0, ST), (j * H, (j + 1) * H)))]
            if any(p.endpoint.shape != shape or p.bounds != bounds or p.value_part != (0, 1)
                   for p, shape, bounds in expected):
                raise ValueError('unsupported position ordered shape/bounds/value layout')
            pm_loaders.append(rank.loader.endpoint.tid)
            pm_chunks.append(chunk.outputs[0].endpoint.tid)
            pm_weights.append(weight.endpoint.tid)
            pm_embeddings.append(rank.embedding.outputs[0].endpoint.tid)
            pm_outs.append(rank.output.endpoint.tid)
            lanes.append(lane)
        sm_ids, sm_weight, sm_out = ids.target.tid, parameter.target.tid, global_out.endpoint.tid
        expected_goal = dict(kind='replicated', sm_tid=sm_weight, pm_tids=pm_weights,
            dim=None, sm_shape=[V, HT], pm_shape=[V, HT])
        if not _same_typed(bu['initial_goal'], expected_goal) or len(bu['bindings']) != T:
            raise ValueError('position bound ordered replicated weight goal mismatch')
        _binding(row['sm_binding'], global_weight, parameter.target.ref, 'sm', raw[0])
        for binding, rank in zip(bu['bindings'], route.ranks, strict=True):
            _binding(binding, rank.embedding.inputs[1], parameter.target.ref, 'pm', raw[1])
        ws, xs, os, aa = (_list(f'q {tid}' for tid in ts)
                         for ts in (pm_weights, pm_chunks, pm_embeddings, pm_outs))
        unit_ids = f'(q {pm_loaders[0]})'
        projection = 'hrels' + '.2' * spec_index + ('.1' if spec_index < len(specs) - 1 else '')
        name = f'embeddingPositionUnit_{sm_out}_{u}'
        facts_name = f'embeddingPositionUnitFacts_{sm_out}_{u}'
        proofs += [f'theorem {facts_name} (s p t q : Store)',
            '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
            '    (h : InitialParameterValues s p) :',
            f'    (t {sm_out}).shape = {[B * D, ST, HT]} ∧',
            f'    (∀ x ∈ {aa}, x.shape = {[B, ST, H]}) ∧',
            f'    chunkPrimDimN 0 {D} {u} (t {sm_out}) =',
            f'    allGatherPrimDimN 2 {T} 0 {aa} := by',
            '  have hrels := initialParameterRelations_of_values t q (initialParameterValues_final s p t q hs hp h)',
            f'  have weights : RelationCompiler.ReplicatedRel (t {sm_weight}) {ws} [{V}, {HT}] := {projection}',
            f'  have fullShape : (t {sm_ids}).shape = [{B * D}, {ST}] :=',
            f'    (inputStoreRelation_{sm_ids}_{lanes[0]} s p t q hs hp).full_shape']
        for j, (tid, lane) in enumerate(zip(pm_loaders, lanes, strict=True)):
            proofs += [f'  have ids{j} : q {tid} = chunkPrimDimN 0 {D} {u} (t {sm_ids}) :=',
                f'    (inputStoreRelation_{sm_ids}_{lane} s p t q hs hp).chunk_values {u} (by change {u} < {D}; decide)']
        proofs += [f'  have unitShape : {unit_ids}.shape = [{B}, {ST}] := by',
            '    rw [ids0]',
            f'    exact chunkPrimDimN_shape 0 {D} {u} (t {sm_ids}) [{B * D}, {ST}] fullShape (by decide)']
        for j in range(T):
            proofs += [f'  have chunk{j} : q {pm_chunks[j]} = chunkPrimDimN 1 {T} {j} {unit_ids} :=',
                f'    (embeddingRouteRead_pm_{pm_chunks[j]} p q hp).trans',
                f'      (congrArg (fun x => chunkPrimDimN 1 {T} {j} x) (ids{j}.trans ids0.symm))',
                f'  have shardShape{j} : (q {pm_chunks[j]}).shape = [{B}, {S}] := by',
                f'    rw [chunk{j}]',
                f'    exact chunkPrimDimN_shape 1 {T} {j} {unit_ids} [{B}, {ST}] unitShape (by decide)',
                f'  have weight{j} : q {pm_weights[j]} = t {sm_weight} :=',
                f'    weights.replica_values (q {pm_weights[j]}) (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true, eq_self])',
                f'  have local{j} : q {pm_embeddings[j]} = fw_embedding (q {pm_chunks[j]}) (t {sm_weight}) :=',
                f'    (embeddingRouteRead_pm_{pm_embeddings[j]} p q hp).trans',
                f'      (congrArg (fun w => fw_embedding (q {pm_chunks[j]}) w) weight{j})']
        chunk_terms = _list(f'chunkPrimDimN 1 {T} {j} {unit_ids}' for j in range(T))
        aa_terms = _list(f'AllToAllSourceFaithful.tensor {T} {j} 1 2 {os}' for j in range(T))
        proofs += [f'  have chunks : {xs} = List.ofFn (fun r : Fin {T} => chunkPrimDimN 1 {T} r.val {unit_ids}) := by',
            f'    change {xs} = {chunk_terms}',
            f'    exact {_cons_equal([f"chunk{j}" for j in range(T)])}',
            f'  have unitGather : {unit_ids} = allGatherPrimDimN 1 {T} 0 {xs} := by',
            '    rw [chunks]',
            f'    exact (TrainVerify.Denote.allGatherPrimDimN_chunks_ofFn 1 {T} {unit_ids}',
            '      (by decide) (by rw [unitShape]; decide) (by rw [unitShape]; decide)).symm',
            f'  have shardShapes : ∀ x ∈ {xs}, x.shape = [{B}, {S}] := by',
            '    intro x hx',
            '    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx',
            '    rcases hx with ' + ' | '.join('rfl' for _ in range(T))]
        proofs += [f'    · exact shardShape{j}' for j in range(T)]
        proofs += [f'  have aaOutputs : {aa} = List.ofFn (fun dst : Fin {T} => AllToAllSourceFaithful.tensor {T} dst.val 1 2 {os}) := by',
            f'    change {aa} = {aa_terms}',
            '    exact ' + _cons_equal([f'embeddingRouteRead_pm_{tid} p q hp' for tid in pm_outs])]
        local = 'List.Forall₂.nil'
        for j in reversed(range(T)):
            local = f'List.Forall₂.cons local{j} ({local})'
        proofs += [f'  exact fw_embedding_dp_tp_position_unit_facts_of_source_eqs {D} {u} {T} {B} {S} {V} {H}',
            f'    (t {sm_ids}) {unit_ids} (t {sm_weight}) {xs} (t {sm_out}) {os} {aa}',
            '    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)',
            '    fullShape weights.full_shape ids0 rfl shardShapes unitGather',
            f'    (embeddingRouteRead_sm_{sm_out} s t hs) ({local}) aaOutputs',
            f'#print axioms {facts_name}',
            f'theorem {name} (s p t q : Store)',
            '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
            '    (h : InitialParameterValues s p) :',
            f'    chunkPrimDimN 0 {D} {u} (t {sm_out}) =',
            f'    allGatherPrimDimN 2 {T} 0 {aa} := by',
            f'  exact ({facts_name} s p t q hs hp h).2.2',
            f'#print axioms {name}']
        records.append(dict(theorem=name, facts_theorem=facts_name, unit=u, spec_index=spec_index, dimensions=dict(D=D, T=T, B=B, S=S, V=V, H=H),
            sm_output_ref=list(global_out.endpoint.ref), sm_output_tid=sm_out,
            sm_input_ref=list(ids.target.ref), sm_input_tid=sm_ids,
            sm_weight_ref=list(parameter.target.ref), sm_weight_tid=sm_weight,
            pm_input_tids=pm_loaders, pm_chunk_tids=pm_chunks, pm_weight_tids=pm_weights,
            pm_embedding_tids=pm_embeddings, pm_output_tids=pm_outs, input_lanes=lanes,
            pm_input_refs=[list(r.loader.endpoint.ref) for r in route.ranks],
            pm_weight_refs=[list(r.embedding.inputs[1].endpoint.ref) for r in route.ranks],
            pm_output_refs=[list(r.output.endpoint.ref) for r in route.ranks],
            global_embedding=asdict(route.global_embedding), routes=[asdict(r) for r in route.ranks]))
    text = '\n'.join(['-- UNCOMPILED: parent-owned kernel check and source-read integration required.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-embedding-position-unit-values-emitted-uncompiled', units=records,
        lean_bytes=len(text.encode('utf-8')), kernel_value_proved=False, proof_admissible=False,
        public_complete=False, torch_refinement=False)
