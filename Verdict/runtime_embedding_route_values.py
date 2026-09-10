"""Complex embedding-route reads on the ORIGINAL successful run's final Store.

The live census is the authority, never its serialized DTO. Only Chunk/exchange
routes are selected; direct embedding reads remain runtime_embedding_values' job.
The parent must import denote.SourceEmbeddingRead and denote.SourcePrimitiveRead
and assemble the original RuntimeWorld nodes/scopes/InputRequests. Generated Lean
is UNCOMPILED until that assembled entry passes the parent's kernel check.
"""
from dataclasses import asdict

from Verdict.runtime_embedding_routes import census
from Verdict.runtime_lineage import _same_typed


def _read(view, label, step, order):
    # Raw CIDs are not source ordinals (nor execution indices).
    nodes = view.nodes()
    matches = [(i, n) for i, n in enumerate(nodes) if tuple(n) == step.node]
    if len(matches) != 1:
        raise ValueError('embedding route original writer not unique')
    index, node = matches[0]
    inputs, outputs = list(view.node_inputs(node)), list(view.node_outputs(node))
    for actual, ports in ((inputs, step.inputs), (outputs, step.outputs)):
        if not _same_typed(
                [(tuple(view.source_tensor(t)), t.tid) for t in actual],
                [(p.endpoint.ref, p.endpoint.tid) for p in ports]):
            raise ValueError('embedding route original ordered ports mismatch')
    if len(outputs) != 1 or str(view.node_opname(node)).split('.')[-1] != step.op:
        raise ValueError('embedding route original operator/output mismatch')
    ins = [t.tid for t in inputs]
    out = outputs[0].tid
    k = order['execution_to_source'].index(index)
    # Match Lean's complete read footprint, INCLUDING the selected step.
    for source_index in order['execution_to_source'][k:]:
        if set(ins) & {t.tid for t in view.node_outputs(nodes[source_index])}:
            raise ValueError('embedding route operand is written by node or suffix')
    name = f'embeddingRouteRead_{label}_{out}'
    requests = f'{label}InputRequests'
    common = (f'{label}Graph {label}Scope {label}Peers {label}Graph.nodes\n'
              f'    {requests} ({requests}.take {k}) ({requests}.drop {k+1}) {label}Node_{index}')
    if step.op == 'FW_embedding':
        if len(ins) != 2:
            raise ValueError('embedding route ordinary embedding arity mismatch')
        value = f'fw_embedding (t {ins[0]}) (t {ins[1]})'
        application = (f'SourceEmbeddingRead.embedding_value_of_split {common} '
                       f'{node.rank} {ins[0]} {ins[1]} {out} s t rfl ?_ rfl ?_ ?_ h')
        obligations = [f'∀ row ∈ {requests}.drop {k}, {tid} ∉ row.1.outs' for tid in ins]
    else:
        ranks = list(step.ranks)
        if (not ranks or not 0 <= step.local_index < len(ranks)
                or ranks[step.local_index] != node.rank):
            raise ValueError('embedding route original group/local_index mismatch')
        if step.op == 'ChunkPrim':
            if len(ins) != 1:
                raise ValueError('embedding route Chunk arity mismatch')
            value = f'chunkPrimDimN {step.chunk_axis} {len(ranks)} {step.local_index} (t {ins[0]})'
            application = (f'SourcePrimitiveRead.chunk_value_of_split {common} '
                           f'{node.rank} {ranks} {ins[0]} {out} {step.chunk_axis} s t rfl ?_ rfl ?_ h')
            obligations = [f'∀ row ∈ {requests}.drop {k}, {ins[0]} ∉ row.1.outs']
        elif step.op == 'AllToAllPrim':
            if step.peers != tuple(zip(step.ranks, ins)):
                raise ValueError('embedding route original ordered peers mismatch')
            value = (f'AllToAllSourceFaithful.tensor {len(ranks)} {step.local_index} '
                     f'{step.gather_axis} {step.split_axis} (({ins} : List Tid).map t)')
            application = (f'SourcePrimitiveRead.allToAll_value_of_split {common} '
                           f'{node.rank} {ranks} {ins} {out} {step.gather_axis} {step.split_axis} '
                           's t rfl ?_ rfl ?_ h')
            obligations = [f'∀ tid ∈ ({ins} : List Tid), ∀ row ∈ {requests}.drop {k}, tid ∉ row.1.outs']
        else:
            raise ValueError('unsupported embedding route source read')
    proof = [f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
             f'    t {out} = {value} := by', f'  apply {application}',
             '  · calc',
             f'      {requests} = {requests}.take {k} ++ {requests}.drop {k} := (List.take_append_drop {k} {requests}).symm',
             '      _ = _ := rfl']
    for obligation in obligations:
        proof.extend([f'  · change {obligation}', '    decide'])
    proof.append(f'#print axioms {name}')
    return proof, dict(theorem=name, world=label, op=step.op, ref=list(step.outputs[0].endpoint.ref),
        node=list(step.node), source_index=index, execution_index=k, input_tids=ins,
        input_refs=[list(p.endpoint.ref) for p in step.inputs], output_tid=out,
        ranks=list(step.ranks), local_index=step.local_index, chunk_axis=step.chunk_axis,
        gather_axis=step.gather_axis, split_axis=step.split_axis,
        peers=[list(p) for p in step.peers], source_writer=step.source_writer,
        source_step=asdict(step))


def render(sm, pm, lineages, validation, execution_order):
    """Render source equations, not cross-world activation equality assumptions."""
    discovered = census(sm, pm, lineages, validation)
    from Verdict.runtime_schedule import build
    canonical_order = {'sm': build(sm), 'pm': build(pm)}
    if not _same_typed(execution_order, canonical_order):
        raise ValueError('embedding route execution order differs from original source schedule')
    proofs, reads, routes, seen = [], [], [], {}
    for route in discovered.routes:
        if not route.ranks or not all(r.chunk is not None and r.exchange is not None for r in route.ranks):
            continue
        steps = [('sm', sm, route.global_embedding)]
        for rank in route.ranks:
            steps.extend(('pm', pm, step) for step in (rank.chunk, rank.embedding, rank.exchange))
        names = []
        for label, view, step in steps:
            ref = step.outputs[0].endpoint.ref
            if ref not in seen:
                proof, row = _read(view, label, step, execution_order[label])
                proofs.extend(proof)
                reads.append(row)
                seen[ref] = row['theorem']
            names.append(seen[ref])
        routes.append(dict(unit=route.unit, positions=list(route.positions),
            batch_key=list(route.batch_key), parameter_key=list(route.parameter_key), reads=names))
    text = '\n'.join(['-- Generated source reads: UNCOMPILED until parent kernel verification.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-embedding-route-values-emitted-uncompiled', reads=reads, routes=routes,
        unavailable=[asdict(x) for x in discovered.unavailable], lean_bytes=len(text.encode('utf-8')),
        proof_admissible=False, public_complete=False, kernel_value_proved=False, torch_refinement=False)
