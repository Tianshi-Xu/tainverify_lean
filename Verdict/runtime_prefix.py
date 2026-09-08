"""Bounded producer-to-first-guard proofs over the authenticated full input schedule.

No tensor is initialized from a captured activation. Only unwritten raw parameter
shapes become conditional premises; values remain arbitrary mathematical tensors.
"""
from Verdict.runtime_lineage import _Index


class PrefixUnavailable(ValueError):
    def __init__(self, reason, **details):
        super().__init__(reason)
        self.details = dict(status='prefix-proof-unavailable', reason=reason, **details)


def render(label, view, raw, world, loaders):
    """Called after bind's canonical world and raw/feed authentication."""
    order = world.receipt['execution_order'][label]['execution_to_source']
    boundary = next((j for j, i in enumerate(order) if str(view.node_opname(view.nodes()[i])).split('.')[-1]
                     in ('AllToAllPrim', 'CROSS_DP_WRED')), None)
    if boundary is None:
        return '', dict(status='prefix-proof-unavailable', reason='no-state-dependent-boundary')
    selected = order[:boundary + 1]
    try:
        return _render(label, view, raw, selected, loaders)
    except PrefixUnavailable as exc:
        return '', dict(exc.details, prefix_nodes=selected, boundary_index=selected[-1],
                        whole_world_option_success=False)


def _render(label, view, raw, selected, loaders):
    index = _Index(view, raw)
    feeds = {row['index']: row for row in loaders if row['world'] == label}
    values = {}; shapes = {}; initial = {}; steps = []; lines = []; names = []
    stem = label + 'Prefix'
    advance = f'(fun row s => stepWithInputs {label}Graph ({label}Scope row.1) ({label}Peers row.1) s row.1 row.2)'
    def theorem(name, args, proof):
        names.append(name)
        lines.extend([f'theorem {name} {args} := {proof}', f'#print axioms {name}'])
    def state(j): return f'({stem}State_{j} init)'
    lines += ['namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
              'open SourceScopedEval', 'set_option maxHeartbeats 500000', 'set_option maxRecDepth 4096',
              f'def {stem}State_0 (init : Store) : Store := init']
    for j, i in enumerate(selected):
        n = view.nodes()[i]; op = str(view.node_opname(n)).split('.')[-1]
        ins = view.node_inputs(n); outs = view.node_outputs(n); node = f'{label}Node_{i}'
        prev = state(j); nxt = state(j+1); feed = 'none'; scope = None
        for t in ins:
            if t.tid not in values:
                ref = tuple(view.source_tensor(t))
                if op != 'FW_embedding' or t != ins[1] or ref in index.writers:
                    raise PrefixUnavailable('unsupported-producer-input', index=i, tid=t.tid, op=op)
                ep = index.endpoint(ref, 'initial'); meta = index.meta.get(ref)
                if not meta or not meta[4] or meta[5]:
                    raise PrefixUnavailable('unauthorized-initial-weight', index=i, tid=t.tid)
                initial[t.tid] = dict(tid=t.tid, ref=list(ref), shape=list(ep.shape), authority='unwritten-raw-parameter')
                values[t.tid] = f'(init {t.tid})'; shapes[t.tid] = list(ep.shape)
        if op == 'DATALOADER':
            if i not in feeds: raise PrefixUnavailable('missing-feed', index=i)
            feed = f'(some {node}_feed)'
            update = f'storeSet {prev} {node}_feed'
            for p in feeds[i]['ports']:
                values[p['tid']] = f'{node}_port{p["port"]}'; shapes[p['tid']] = p['shape']
            proof = f'by\n  exact {node}_scoped_step {prev}'
        elif op == 'FW_embedding':
            if len(ins) != 2 or len(outs) != 1:
                raise PrefixUnavailable('unsupported-embedding-schema', index=i)
            x, w = ins; out, = outs
            value = f'fw_embedding {values[x.tid]} {values[w.tid]}'
            values[out.tid] = f'({value})'; shapes[out.tid] = shapes[x.tid] + [shapes[w.tid][-1]]
            update = f'storeSet {prev} [({out.tid}, {value})]'
            proof = 'by\n  change some (applyNode _ _ _) = _\n  rfl'
        elif op == 'ChunkPrim':
            scope = view.chunk_scopes[n]; x, = ins; out, = outs
            rs = list(scope.ranks); dim = scope.dim; sh = shapes[x.tid].copy()
            if dim >= len(sh) or sh[dim] <= 0 or sh[dim] % len(rs):
                raise PrefixUnavailable('chunk-shape-contract', index=i, computed_shape=sh)
            sh[dim] //= len(rs)
            value = f'chunkPrimDimN {dim} {len(rs)} {scope.local_index} {values[x.tid]}'
            values[out.tid] = f'({value})'; shapes[out.tid] = sh
            update = f'storeSet {prev} [({out.tid}, {value})]'
            proof = (f'by\n  change GroupScopedEval.step {label}Graph (.group (some {rs})) {prev} {node} = _\n'
                     f'  rw [GroupScopedEval.step_scoped _ _ _ {rs} (by decide) (by rfl)]\n  rfl')
        elif op == 'AllToAllPrim':
            scope = view.collective_scopes[n]; rs = list(scope.ranks); dim, odim = scope.params; out, = outs
            sh = shapes[ins[0].tid].copy()
            if (len(ins) != len(rs) or any(shapes[t.tid] != sh for t in ins) or
                    max(dim, odim) >= len(sh) or sh[odim] <= 0 or sh[odim] % len(rs)):
                raise PrefixUnavailable('alltoall-shape-contract', index=i, computed_shapes=[shapes[t.tid] for t in ins])
            operand_shape = sh.copy(); sh[odim] //= len(rs); sh[dim] *= len(rs)
            value = f'AllToAllSourceFaithful.tensor {len(rs)} {scope.local_index} {dim} {odim} [{", ".join(values[t.tid] for t in ins)}]'
            values[out.tid] = f'({value})'; shapes[out.tid] = sh
            update = f'AllToAllSourceFaithful.localStep {rs} {prev} {node} {dim} {odim}'
            proof = (f'by\n  change (AllToAllSourceFaithful.step {label}Graph (some {rs}) ({label}Peers {node}) {prev} {node}).toOption = _\n'
                     f'  rw [AllToAllSourceFaithful.step_valid _ _ _ _ _ {dim} {odim} {out.tid} (by decide) ({stem}Guard init hInitShapes)]\n  rfl')
        else:
            raise PrefixUnavailable('unsupported-producer', index=i, op=op)
        for t in outs:
            if shapes[t.tid] != list(view.tensor_shape(t)):
                raise PrefixUnavailable('computed-source-shape-mismatch', index=i, tid=t.tid,
                                        computed_shape=shapes[t.tid], source_shape=list(view.tensor_shape(t)))
        if op == 'AllToAllPrim':
            premises = list(initial.values())
            goal = ' ∧ '.join(f'(init {p["tid"]}).shape = {p["shape"]}' for p in premises) or 'True'
            lines.append(f'def {stem}InitShapes (init : Store) : Prop := {goal}')
            hs = [f'h{q}' for q in range(len(premises))]
            destruct = f'  rcases hInitShapes with ⟨{", ".join(hs)}⟩\n' if len(hs)>1 else (f'  have h0 := hInitShapes\n' if hs else '')
            defs = ', '.join(f'{stem}State_{q}' for q in range(j+1))
            feeddefs = ', '.join(f'{label}Node_{fi}_feed, {label}Node_{fi}_port0, {label}Node_{fi}_port1' for fi in feeds if fi in selected)
            simplify = f'{defs}, {feeddefs}, storeSet, List.find?, fw_embedding_shape, chunkPrimDimN, Tensor.mkShape, lastD, '+', '.join(hs)
            theorem(stem+'Guard', f'(init : Store) (hInitShapes : {stem}InitShapes init) : AllToAllSourceFaithful.NodeContract {rs} ({label}Peers {node}) {prev} {node} {dim} {odim} {out.tid}',
                    f'by\n  refine ⟨rfl, rfl, rfl, rfl, ?_⟩\n  refine ⟨by decide, rfl, {operand_shape}, ?_, by decide, by decide, by decide, by decide⟩\n'+destruct+
                    f'  simp [{node}, {simplify}]')
        lines.append(f'def {stem}State_{j+1} (init : Store) : Store := {update}')
        condition = f'(hInitShapes : {stem}InitShapes init) ' if op == 'AllToAllPrim' else ''
        theorem(f'{stem}Step_{j}', f'(init : Store) {condition}: stepWithInputs {label}Graph ({label}Scope {node}) ({label}Peers {node}) {prev} {node} {feed} = some {nxt}', proof)
        steps.append(f'{stem}Step_{j} init'+(' hInitShapes' if condition else ''))
    length = len(selected); final = state(length)
    args = f'(init : Store) (hInitShapes : {stem}InitShapes init)'
    run = f'runUsing {advance} ({label}InputRequests.take {length}) (some init)'
    theorem(stem+'Success', f'{args} : {run} = some {final}',
            'by\n  '+f'change runUsing {advance} [{", ".join(f"({label}Node_{i}, "+(f"some {label}Node_{i}_feed" if i in feeds else "none")+")" for i in selected)}] (some ({stem}State_0 init)) = _\n'+
            '  simp only [runUsing, List.foldl_cons, List.foldl_nil, Option.bind_some]\n  '+ '\n  '.join(f'rw [{step}]'+('\n  simp only [Option.bind_some]' if q < len(steps)-1 else '') for q, step in enumerate(steps)))
    theorem(stem+'Output', f'(init : Store) : {final} {out.tid} = {value}', 'by\n  rfl')
    theorem(stem+'OutputShape', f'{args} : ({final} {out.tid}).shape = {sh}',
            f'by\n  rw [{stem}Output]\n  rw [AllToAllSourceFaithful.tensor_shape _ _ _ _ _ _ (by decide)]\n'+destruct+
            f'  simp [fw_embedding_shape, chunkPrimDimN, Tensor.mkShape, lastD, {feeddefs}, '+', '.join(hs)+']')
    theorem(stem+'Frame', f'{args} (tid : Tid) (ht : ∀ row ∈ {label}InputRequests.take {length}, tid ∉ row.1.outs) : {final} tid = init tid',
            f'SourceScopedPrefix.frame {label}Graph {label}Scope {label}Peers _ init {final} tid ht ({stem}Success init hInitShapes)')
    theorem(stem+'Continuation', f'{args} : {label}DenoteWithInputs init = runUsing {advance} ({label}InputRequests.drop {length}) (some {final})',
            f'by\n  rw [{label}DenoteWithInputs_entry]\n  exact SourceScopedPrefix.continuation _ _ {length} init {final} ({stem}Success init hInitShapes)')
    lines += ['end', 'end TrainVerify.Denote.RuntimeWorld', '']
    return '\n'.join(lines), dict(status='conditional-prefix-emitted', prefix_nodes=selected,
        prefix_length=length, boundary_index=selected[-1], initial_premises=list(initial.values()),
        output_tid=out.tid, output_shape=sh, kernel_checks=names, kernel_checked=False,
        whole_world_option_success=False, external_adapter_proved=False)
