"""Maximal contiguous computed prefixes of the authenticated full input schedule.

Only unwritten raw parameter shapes are premises. Values are computed from the
actual feeds and arbitrary initial weights, in one Store chain. Unsupported nodes
are frontiers, never skipped. Small read/value-shape lemmas bound elaboration.
"""
from Verdict.runtime_lineage import _Index


class PrefixUnavailable(ValueError):
    def __init__(self, reason, **details):
        super().__init__(reason)
        self.details = dict(status='prefix-proof-unavailable', reason=reason, **details)


def render(label, view, raw, world, loaders):
    """Called after bind's canonical world and raw/feed authentication."""
    order = world.receipt['execution_order'][label]['execution_to_source']
    if not any(str(view.node_opname(view.nodes()[i])).split('.')[-1]
               in ('AllToAllPrim', 'CROSS_DP_WRED') for i in order):
        return '', dict(status='prefix-proof-unavailable', reason='no-state-dependent-boundary')
    index = _Index(view, raw)
    feeds = {row['index']: row for row in loaders if row['world'] == label}
    missing = {row['index']: row['reason'] for row in world.receipt['missing'] if row['world'] == label}
    shapes = {}; initial = {}; rows = []; frontier = None
    # Commit each node's inferred shapes/premises only after all checks succeed.
    for j, i in enumerate(order):
        n = view.nodes()[i]; op = str(view.node_opname(n)).split('.')[-1]
        ins = view.node_inputs(n); outs = view.node_outputs(n)
        ss = dict(shapes); ii = dict(initial)
        try:
            if op not in ('DATALOADER', 'FW_embedding', 'ChunkPrim', 'AllToAllPrim', 'FW_add', 'FW_multiref'):
                raise PrefixUnavailable('unsupported-producer', op=op)
            if i in missing and op != 'DATALOADER':
                raise PrefixUnavailable(missing[i], op=op)
            if not outs or (op == 'FW_embedding' and (len(ins) != 2 or len(outs) != 1)) or (op == 'FW_add' and (len(ins) not in (1, 2) or len(outs) != 1)) or (op == 'FW_multiref' and (len(ins) != 1 or view.node_kwargs(n).get('times', len(outs)) != len(outs))):
                raise PrefixUnavailable('unsupported-producer-schema', op=op)
            for t in ins:
                if t.tid not in ss:
                    ref = tuple(view.source_tensor(t))
                    if op != 'FW_embedding' or t != ins[1] or ref in index.writers:
                        raise PrefixUnavailable('unsupported-producer-input', tid=t.tid, op=op)
                    ep = index.endpoint(ref, 'initial'); meta = index.meta.get(ref)
                    if not meta or not meta[4] or meta[5]:
                        raise PrefixUnavailable('unauthorized-initial-weight', tid=t.tid)
                    ii[t.tid] = dict(tid=t.tid, ref=list(ref), shape=list(ep.shape), authority='unwritten-raw-parameter')
                    ss[t.tid] = list(ep.shape)
            scope = None
            if op == 'DATALOADER':
                if i not in feeds: raise PrefixUnavailable('missing-feed')
                output_shapes = [p['shape'] for p in feeds[i]['ports']]
            elif op == 'FW_embedding':
                output_shapes = [ss[ins[0].tid] + [ss[ins[1].tid][-1]]]
            elif op in ('ChunkPrim', 'AllToAllPrim'):
                scope = (view.chunk_scopes if op == 'ChunkPrim' else view.collective_scopes)[n]
                rs = list(scope.ranks); sh = ss[ins[0].tid].copy()
                dim, odim = (scope.dim, scope.dim) if op == 'ChunkPrim' else scope.params
                if (len(outs) != 1 or len(ins) != (1 if op == 'ChunkPrim' else len(rs)) or
                        any(ss[t.tid] != sh for t in ins) or max(dim, odim) >= len(sh) or
                        sh[odim] <= 0 or sh[odim] % len(rs)):
                    raise PrefixUnavailable('chunk-shape-contract' if op == 'ChunkPrim' else 'alltoall-shape-contract', computed_shapes=[ss[t.tid] for t in ins])
                sh[odim] //= len(rs)
                if op == 'AllToAllPrim': sh[dim] *= len(rs)
                output_shapes = [sh]
            elif op == 'FW_add':
                sh = ss[ins[0].tid]
                if len(ins) == 2:
                    other = ss[ins[1].tid]; size = max(len(sh), len(other))
                    sh = [max(a, b) for a, b in zip([1]*(size-len(sh))+sh, [1]*(size-len(other))+other)]
                output_shapes = [sh]
            else:
                output_shapes = [ss[ins[0].tid]] * len(outs)
            for t, sh in zip(outs, output_shapes):
                if sh != list(view.tensor_shape(t)):
                    raise PrefixUnavailable('computed-source-shape-mismatch', tid=t.tid, computed_shape=sh, source_shape=list(view.tensor_shape(t)))
                ss[t.tid] = sh
            rows.append(dict(index=i, op=op, ins=ins, outs=outs, scope=scope,
                             input_shapes=[ss[t.tid] for t in ins], output_shapes=output_shapes))
            shapes, initial = ss, ii
        except PrefixUnavailable as exc:
            frontier = dict(exc.details, index=i, source_index=i, execution_index=j, op=op)
            break
    if not any(r['op'] == 'AllToAllPrim' for r in rows):
        return '', dict(frontier or dict(status='prefix-proof-unavailable', reason='no-supported-guard'),
                        prefix_nodes=[r['index'] for r in rows], frontier=frontier,
                        whole_world_option_success=False)
    return _render(label, rows, feeds, initial, frontier)


def _render(label, rows, feeds, initial, frontier):
    stem = label + 'Prefix'; lines = []; names = []; guards = []; steps = []
    values = {tid: f'(init {tid})' for tid in initial}; writers = {}; shape_proofs = {}
    def state(j): return f'({stem}State_{j} init)'
    def theorem(name, args, proof):
        names.append(name)
        lines.extend([f'theorem {name} {args} := {proof}', f'#print axioms {name}'])
    advance = f'(fun row s => stepWithInputs {label}Graph ({label}Scope row.1) ({label}Peers row.1) s row.1 row.2)'
    args = f'(init : Store) (hInitShapes : {stem}InitShapes init)'
    goal = ' ∧ '.join(f'(init {p["tid"]}).shape = {p["shape"]}' for p in initial.values()) or 'True'
    lines += ['namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
              'open SourceScopedEval', 'set_option maxHeartbeats 500000', 'set_option maxRecDepth 4096',
              f'def {stem}InitShapes (init : Store) : Prop := {goal}',
              f'def {stem}State_0 (init : Store) : Store := init']
    hs = [f'h{q}' for q in range(len(initial))]
    destruct = f'  rcases hInitShapes with ⟨{", ".join(hs)}⟩\n' if len(hs)>1 else ('  have h0 := hInitShapes\n' if hs else '')
    for q, (tid, p) in enumerate(initial.items()):
        name = f'{stem}InitialShape_{q}'
        theorem(name, f'{args} : (init {tid}).shape = {p["shape"]}', 'by\n'+destruct+f'  exact h{q}')
        shape_proofs[tid] = f'{name} init hInitShapes'
    for j, row in enumerate(rows):
        i, op, ins, outs, scope = (row[k] for k in ('index','op','ins','outs','scope'))
        node = f'{label}Node_{i}'; prev = state(j); nxt = state(j+1)
        reads = []
        for p, t in enumerate(ins):
            name = f'{stem}Read_{j}_{p}'; reads.append(f'{name} init')
            proof = 'by\n  rfl' if t.tid not in writers else f'by\n  change {state(writers[t.tid][0]+1)} {t.tid} = _\n  exact {writers[t.tid][1]} init'
            theorem(name, f'(init : Store) : {prev} {t.tid} = {values[t.tid]}', proof)
        v = [values[t.tid] for t in ins]; actual = [f'({prev} {t.tid})' for t in ins]
        def expressions(xs):
            if op == 'DATALOADER': return [f'{node}_port{p["port"]}' for p in feeds[i]['ports']]
            if op == 'FW_embedding': return [f'fw_embedding {xs[0]} {xs[1]}']
            if op == 'ChunkPrim': return [f'chunkPrimDimN {scope.dim} {len(scope.ranks)} {scope.local_index} {xs[0]}']
            if op == 'AllToAllPrim': return [f'AllToAllSourceFaithful.tensor {len(scope.ranks)} {scope.local_index} {scope.params[0]} {scope.params[1]} [{", ".join(xs)}]']
            if op == 'FW_add': return [xs[0] if len(xs)==1 else f'elemwiseAdd {xs[0]} {xs[1]}']
            return [xs[0]] * len(outs)
        pure, computed = expressions(v), expressions(actual)
        for p, value in enumerate(pure):
            lines.append(f'def {stem}Value_{j}_{p} (init : Store) : Tensor := {value}')
        feed = f'(some {node}_feed)' if op == 'DATALOADER' else 'none'
        update = f'storeSet {prev} ['+', '.join(f'({t.tid}, {value})' for t, value in zip(outs, computed))+']'
        if op == 'DATALOADER':
            update = f'storeSet {prev} {node}_feed'
            proof = f'by\n  exact {node}_scoped_step {prev}'
        elif op == 'AllToAllPrim':
            rs = list(scope.ranks); dim, odim = scope.params; out, = outs
            guard = f'{stem}Guard_{j}'
            theorem(guard, f'{args} : AllToAllSourceFaithful.NodeContract {rs} ({label}Peers {node}) {prev} {node} {dim} {odim} {out.tid}',
                    f'by\n  refine ⟨rfl, rfl, rfl, rfl, ?_⟩\n  refine ⟨by decide, rfl, {row["input_shapes"][0]}, ?_, by decide, by decide, by decide, by decide⟩\n  simp [{node}, '+', '.join(reads+[shape_proofs[t.tid] for t in ins])+']')
            guards.append(dict(index=i, source_index=i, execution_index=j, theorem=guard, state=f'{stem}State_{j}', input_tids=[t.tid for t in ins], operand_shapes=row['input_shapes'], output_tid=out.tid, output_shape=row['output_shapes'][0]))
            update = f'AllToAllSourceFaithful.localStep {rs} {prev} {node} {dim} {odim}'
            proof = (f'by\n  change (AllToAllSourceFaithful.step {label}Graph (some {rs}) ({label}Peers {node}) {prev} {node}).toOption = _\n'
                     f'  rw [AllToAllSourceFaithful.step_valid _ _ _ _ _ {dim} {odim} {out.tid} (by decide) ({guard} init hInitShapes)]\n  rfl')
        elif op == 'ChunkPrim':
            rs = list(scope.ranks)
            proof = (f'by\n  change GroupScopedEval.step {label}Graph (.group (some {rs})) {prev} {node} = _\n'
                     f'  rw [GroupScopedEval.step_scoped _ _ _ {rs} (by decide) (by rfl)]\n  rfl')
        else:
            proof = 'by\n  change some (applyNode _ _ _) = _\n  rfl'
        lines.append(f'def {stem}State_{j+1} (init : Store) : Store := {update}')
        condition = op == 'AllToAllPrim'
        theorem(f'{stem}Step_{j}', f'{args if condition else "(init : Store)"} : stepWithInputs {label}Graph ({label}Scope {node}) ({label}Peers {node}) {prev} {node} {feed} = some {nxt}', proof)
        steps.append(f'{stem}Step_{j} init'+(' hInitShapes' if condition else ''))
        input_shapes = [shape_proofs[t.tid] for t in ins]
        for p, (t, value, sh) in enumerate(zip(outs, computed, row['output_shapes'])):
            vn = f'{stem}Value_{j}_{p}'; on = f'{stem}Written_{j}_{p}'; sn = f'{stem}Shape_{j}_{p}'
            theorem(on, f'(init : Store) : {nxt} {t.tid} = {vn} init',
                    f'by\n  change {value} = {vn} init\n  simp only [{vn}'+(', '+', '.join(reads) if reads else '')+']')
            shape_defs = [vn, 'fw_embedding_shape', 'chunkPrimDimN', 'Tensor.mkShape', 'lastD', 'elemwiseAdd', 'outShape2'] + input_shapes
            if op == 'DATALOADER': shape_defs.append(f'{node}_port{p}')
            shape_start = f'by\n  unfold {vn}\n  rw [AllToAllSourceFaithful.tensor_shape _ _ _ _ _ _ (by decide)]\n' if op == 'AllToAllPrim' else 'by\n'
            theorem(sn, f'{args} : ({vn} init).shape = {sh}', shape_start+'  simp ['+', '.join(shape_defs)+']')
            values[t.tid] = f'({vn} init)'; writers[t.tid] = (j, on); shape_proofs[t.tid] = f'{sn} init hInitShapes'
    selected = [r['index'] for r in rows]; length = len(rows); final = state(length)
    run = f'runUsing {advance} ({label}InputRequests.take {length}) (some init)'
    theorem(stem+'Success', f'{args} : {run} = some {final}',
            'by\n  '+f'change runUsing {advance} [{", ".join(f"({label}Node_{i}, "+(f"some {label}Node_{i}_feed" if i in feeds else "none")+")" for i in selected)}] (some ({stem}State_0 init)) = _\n'+
            '  simp only [runUsing, List.foldl_cons, List.foldl_nil, Option.bind_some]\n  '+ '\n  '.join(f'rw [{step}]'+('\n  simp only [Option.bind_some]' if q < len(steps)-1 else '') for q, step in enumerate(steps)))
    out = rows[-1]['outs'][-1]; sh = shapes_out = rows[-1]['output_shapes'][-1]
    theorem(stem+'Output', f'(init : Store) : {final} {out.tid} = {values[out.tid]}', f'{writers[out.tid][1]} init')
    theorem(stem+'OutputShape', f'{args} : ({final} {out.tid}).shape = {sh}', f'by\n  rw [{stem}Output]\n  exact {shape_proofs[out.tid]}')
    theorem(stem+'Frame', f'{args} (tid : Tid) (ht : ∀ row ∈ {label}InputRequests.take {length}, tid ∉ row.1.outs) : {final} tid = init tid',
            f'SourceScopedPrefix.frame {label}Graph {label}Scope {label}Peers _ init {final} tid ht ({stem}Success init hInitShapes)')
    theorem(stem+'Continuation', f'{args} : {label}DenoteWithInputs init = runUsing {advance} ({label}InputRequests.drop {length}) (some {final})',
            f'by\n  rw [{label}DenoteWithInputs_entry]\n  exact SourceScopedPrefix.continuation _ _ {length} init {final} ({stem}Success init hInitShapes)')
    lines += ['end', 'end TrainVerify.Denote.RuntimeWorld', '']
    return '\n'.join(lines), dict(status='conditional-prefix-emitted', prefix_nodes=selected,
        prefix_length=length, boundary_index=guards[-1]['index'], guards=guards, frontier=frontier,
        initial_premises=list(initial.values()), output_tid=out.tid, output_shape=shapes_out,
        kernel_checks=names, kernel_checked=False, whole_world_option_success=False, external_adapter_proved=False)
