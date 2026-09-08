"""Maximal contiguous computed prefixes of the authenticated full input schedule.

Only unwritten raw parameter shapes are premises. Values are computed from the
actual feeds and arbitrary initial weights, in one Store chain. Unsupported nodes
are frontiers, never skipped. Small read/value-shape lemmas bound elaboration.
"""
from math import prod
from dataclasses import dataclass
from Verdict.runtime_lineage import _Index


PROOF_BYTE_BUDGET = 40000
PROOF_DECLARATION_BUDGET = 80
# Bound fold elaboration independently of graph, operator and packing budgets.
RUN_STEP_BUDGET = 16
PREFIX_MODULE = 'TrainVerifyRuntimePrefix'
_HEADER = '\n'.join(['namespace TrainVerify.Denote.RuntimeWorld',
    'noncomputable section', 'open SourceScopedEval',
    'set_option maxHeartbeats 500000', 'set_option maxRecDepth 4096']) + '\n'
_FOOTER = '\nend\nend TrainVerify.Denote.RuntimeWorld\n'


@dataclass(frozen=True)
class ProofGroup:
    """An indivisible initializer, node proof, or final assembly declaration group."""
    text: str
    declarations: int
    opaque: tuple
    final: bool = False


def pack_proofs(prefixes):
    """Maximal sequential packing; every edge imports the actual prior chain.

    Budgets cover declaration bodies (import/local-attribute scaffolding is not
    a declaration). A single oversized group is an error, never split by syntax.
    """
    from Verdict.runtime_world import WORLD_DATA_MODULE
    imports = f'import {WORLD_DATA_MODULE}\nimport denote.SourceScopedPrefix\n'
    groups = [g for prefix in prefixes for g in prefix]
    def fits(gs):
        return (sum(len(g.text.encode('utf-8')) for g in gs) <= PROOF_BYTE_BUDGET
                and sum(g.declarations for g in gs) <= PROOF_DECLARATION_BUDGET)
    if any(not fits([g]) for g in groups):
        raise ValueError('prefix atomic declaration group exceeds proof budget')
    if fits(groups):
        return imports + _HEADER + '\n'.join(g.text for g in groups) + _FOOTER, {}
    chunks = []; current = []; finals = []
    for g in groups:
        if g.final:
            finals.append(g)
            continue
        if current and not fits(current + [g]):
            chunks.append(current); current = []
        current.append(g)
    if current: chunks.append(current)
    if not fits(finals):
        raise ValueError('prefix final assembly exceeds proof budget')
    supporting = {}; opaque = []; previous = None
    def source(gs):
        edge = f'import {previous}\n' if previous else ''
        attrs = ''.join(f'attribute [local irreducible] {n}\n' for n in opaque)
        return imports + edge + _HEADER + attrs + '\n'.join(g.text for g in gs) + _FOOTER
    for index, chunk in enumerate(chunks):
        name = f'{PREFIX_MODULE}{index:04d}'
        supporting[name+'.lean'] = source(chunk)
        opaque.extend(n for g in chunk for n in g.opaque)
        previous = name
    return source(finals), supporting


class PrefixUnavailable(ValueError):
    def __init__(self, reason, **details):
        super().__init__(reason)
        self.details = dict(status='prefix-proof-unavailable', reason=reason, **details)


def render(label, view, raw, world, loaders, *, structured=False, seed_inventories=None):
    """Called after bind's canonical world and raw/feed authentication."""
    order = world.receipt['execution_order'][label]['execution_to_source']
    if not any(str(view.node_opname(view.nodes()[i])).split('.')[-1]
               in ('AllToAllPrim', 'CROSS_DP_WRED') for i in order):
        return '', dict(status='prefix-proof-unavailable', reason='no-state-dependent-boundary')
    index = _Index(view, raw)
    feeds = {row['index']: row for row in loaders if row['world'] == label}
    missing = {row['index']: row['reason'] for row in world.receipt['missing'] if row['world'] == label}
    seeds = None if seed_inventories is None else seed_inventories[label]
    seed_ids = {} if seeds is None else {row['tid']: q for q, row in enumerate(seeds)}
    shapes = {tid: [1] for tid in seed_ids}; initial = {}; rows = []; frontier = None
    # Commit each node's inferred shapes/premises only after all checks succeed.
    for j, i in enumerate(order):
        n = view.nodes()[i]; op = str(view.node_opname(n)).split('.')[-1]
        ins = view.node_inputs(n); outs = view.node_outputs(n)
        ss = dict(shapes); ii = dict(initial)
        try:
            if op == 'BW_sum' and seeds is not None:
                if (len(ins) != 2 or len(outs) != 1
                        or ins[0].tid not in seed_ids
                        or ins[1].tid not in {t.tid for row in rows for t in row['outs']}
                        or list(n) != seeds[seed_ids[ins[0].tid]]['consumer']
                        or dict(view.node_kwargs(n)) not in ({}, {'__consts': []})):
                    raise PrefixUnavailable('unsupported-seed-sum-contract', op=op)
            elif op not in ('DATALOADER', 'FW_embedding', 'ChunkPrim', 'AllToAllPrim', 'FW_add', 'FW_multiref', 'FW_layernorm', 'FW_linear', 'AllGatherPrim', 'FW_view', 'FW_reshape', 'FW_transpose', 'FW_matmul', 'FW_div', 'FW_softmax', 'FW_contiguous', 'FW_gelu', 'FW_sum', 'ReduceScatterPrim', 'AllReducePrim'):
                raise PrefixUnavailable('unsupported-producer', op=op)
            if i in missing and op != 'DATALOADER':
                raise PrefixUnavailable(missing[i], op=op)
            if not outs or (op == 'FW_embedding' and (len(ins) != 2 or len(outs) != 1)) or (op == 'FW_add' and (len(ins) not in (1, 2) or len(outs) != 1)) or (op == 'FW_multiref' and (len(ins) != 1 or view.node_kwargs(n).get('times', len(outs)) != len(outs))):
                raise PrefixUnavailable('unsupported-producer-schema', op=op)
            for port, t in enumerate(ins):
                if t.tid not in ss:
                    ref = tuple(view.source_tensor(t))
                    if port not in {'FW_embedding': (1,), 'FW_layernorm': (1, 2), 'FW_linear': (1,)}.get(op, ()) or ref in index.writers:
                        raise PrefixUnavailable('unsupported-producer-input', tid=t.tid, op=op)
                    ep = index.endpoint(ref, 'initial'); meta = index.meta.get(ref)
                    if not meta or not meta[4] or meta[5]:
                        raise PrefixUnavailable('unauthorized-initial-weight', tid=t.tid)
                    ii[t.tid] = dict(tid=t.tid, ref=list(ref), shape=list(ep.shape), authority='unwritten-raw-parameter')
                    ss[t.tid] = list(ep.shape)
            scope = None; params = None
            if op == 'DATALOADER':
                if i not in feeds: raise PrefixUnavailable('missing-feed')
                output_shapes = [p['shape'] for p in feeds[i]['ports']]
            elif op == 'FW_embedding':
                output_shapes = [ss[ins[0].tid] + [ss[ins[1].tid][-1]]]
            elif op in ('ChunkPrim', 'AllToAllPrim', 'ReduceScatterPrim'):
                scope = (view.chunk_scopes if op == 'ChunkPrim' else view.collective_scopes)[n]
                rs = list(scope.ranks); sh = ss[ins[0].tid].copy()
                dim, odim = (scope.dim, scope.dim) if op == 'ChunkPrim' else ((scope.params[0], scope.params[0]) if op == 'ReduceScatterPrim' else scope.params)
                if (len(outs) != 1 or len(ins) != (1 if op == 'ChunkPrim' else len(rs)) or
                        any(ss[t.tid] != sh for t in ins) or max(dim, odim) >= len(sh) or
                        sh[odim] <= 0 or sh[odim] % len(rs)):
                    raise PrefixUnavailable('chunk-shape-contract' if op == 'ChunkPrim' else 'reducescatter-shape-contract' if op == 'ReduceScatterPrim' else 'alltoall-shape-contract', computed_shapes=[ss[t.tid] for t in ins])
                sh[odim] //= len(rs)
                if op == 'AllToAllPrim': sh[dim] *= len(rs)
                output_shapes = [sh]
            elif op == 'AllReducePrim':
                scope = view.collective_scopes[n]
                if (len(outs) != 1 or not ins or len(ins) != len(scope.ranks)
                        or scope.params or not 0 <= scope.local_index < len(scope.ranks)
                        or any(ss[t.tid] != ss[ins[0].tid] for t in ins)):
                    raise PrefixUnavailable('allreduce-shape-contract')
                output_shapes = [ss[ins[0].tid].copy()]
            elif op == 'AllGatherPrim':
                scope = view.collective_scopes[n]
                sh = ss[ins[0].tid].copy(); dim, = scope.params
                if (len(outs) != 1 or len(ins) != len(scope.ranks) or dim >= len(sh)
                        or any(ss[t.tid] != sh for t in ins)):
                    raise PrefixUnavailable('allgather-shape-contract')
                sh[dim] *= len(scope.ranks)
                output_shapes = [sh]
            elif op in ('FW_view', 'FW_reshape', 'FW_transpose'):
                from Verdict import graph_to_lean as c
                from Verdict.runtime_world import _ordinary
                params, reason = _ordinary(view, n, c._get_node_params)
                if reason or len(ins) != 1 or len(outs) != 1:
                    raise PrefixUnavailable(reason or 'unsupported-producer-schema')
                sh = ss[ins[0].tid]
                if op == 'FW_transpose':
                    if len(params) != 2 or any(d >= len(sh) for d in params):
                        raise PrefixUnavailable('layout-axis-contract')
                    target = sh.copy(); a, b = params
                    target[a], target[b] = target[b], target[a]
                else:
                    # Lowering uses output metadata; independently validate the
                    # literal source request, never infer it from that metadata.
                    kw = view.node_kwargs(n)
                    keys = [key for key in ('size', 'shape') if key in kw]
                    if len(keys) != 1 or (op == 'FW_view' and keys != ['size']):
                        raise PrefixUnavailable('layout-source-params')
                    requested = kw[keys[0]]
                    if not isinstance(requested, (tuple, list)) or not requested or any(type(d) is not int or d < -1 for d in requested) or requested.count(-1) > 1:
                        raise PrefixUnavailable('layout-source-params')
                    target = list(requested)
                    if -1 in target:
                        known = prod(d for d in target if d != -1)
                        if known <= 0 or prod(sh) % known:
                            raise PrefixUnavailable('layout-product-contract')
                        target[target.index(-1)] = prod(sh) // known
                    if prod(target) != prod(sh):
                        raise PrefixUnavailable('layout-product-contract')
                    if target != params:
                        raise PrefixUnavailable('layout-source-params')
                output_shapes = [target]
            elif op in ('FW_matmul', 'FW_div', 'FW_softmax'):
                from Verdict import graph_to_lean as c
                from Verdict.runtime_world import _ordinary
                params, reason = _ordinary(view, n, c._get_node_params)
                if reason:
                    raise PrefixUnavailable(reason)
                sh = ss[ins[0].tid]
                if op == 'FW_matmul':
                    other = ss[ins[1].tid]
                    # Denote indexes both operands with the same flat batch
                    # offset. Broadcasting (even singleton batches) is not its
                    # semantics. Infer only from computed operand shapes.
                    if (len(sh) not in (2, 3, 4) or len(other) != len(sh)
                            or sh[:-2] != other[:-2] or sh[-1] != other[-2]):
                        raise PrefixUnavailable('matmul-shape-contract', computed_shapes=[sh, other])
                    output_shapes = [sh[:-1] + [other[-1]]]
                else:
                    if op == 'FW_softmax' and (not sh or sh[-1] <= 0):
                        raise PrefixUnavailable('softmax-shape-contract')
                    output_shapes = [sh]
            elif op == 'BW_sum':
                output_shapes = [ss[ins[1].tid]]
            elif op == 'FW_sum':
                # Denote's existing full-reduction scalar representation.
                output_shapes = [[1]]
            elif op in ('FW_contiguous', 'FW_gelu'):
                output_shapes = [ss[ins[0].tid]]
            elif op == 'FW_linear':
                sh, weight = (ss[t.tid] for t in ins)
                if len(sh) not in (2, 3) or len(weight) != 2 or sh[-1] != weight[1]:
                    raise PrefixUnavailable('linear-shape-contract')
                output_shapes = [sh[:-1] + [weight[0]]]
            elif op == 'FW_layernorm':
                sh = ss[ins[0].tid]
                if not sh or any(ss[t.tid] != [sh[-1]] for t in ins[1:]):
                    raise PrefixUnavailable('layernorm-shape-contract')
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
                             input_shapes=[ss[t.tid] for t in ins], output_shapes=output_shapes, params=params))
            shapes, initial = ss, ii
        except PrefixUnavailable as exc:
            frontier = dict(exc.details, index=i, source_index=i, execution_index=j, op=op)
            break
    if not any(r['op'] == 'AllToAllPrim' for r in rows):
        return '', dict(frontier or dict(status='prefix-proof-unavailable', reason='no-supported-guard'),
                        prefix_nodes=[r['index'] for r in rows], frontier=frontier,
                        whole_world_option_success=False)
    return _render(label, rows, feeds, initial, frontier, structured=structured, seeds=seeds)


def _render(label, rows, feeds, initial, frontier, *, structured=False, seeds=None):
    stem = label + ('Prefix' if seeds is None else 'SeededPrefix'); lines = []; names = []; guards = []; steps = []
    groups = []; definitions = []; opaque = []; group_start = 0
    def definition(text):
        definitions.append(text)
        lines.append(text)
    def group(final=False):
        nonlocal group_start
        groups.append(ProofGroup('\n'.join(lines), len(definitions) + len(names) - group_start,
                                 tuple(opaque), final))
        lines.clear(); definitions.clear(); opaque.clear(); group_start = len(names)
    values = {tid: f'(init {tid})' for tid in initial}; writers = {}; shape_proofs = {}
    seed_ids = {} if seeds is None else {row['tid']: q for q, row in enumerate(seeds)}
    values.update({tid: 'unitSeed' for tid in seed_ids})
    shape_proofs.update({tid: 'unitSeed_shape' for tid in seed_ids})
    initial_store = 'init' if seeds is None else f'({label}InitialWithSeeds init)'
    initial_reads = {}
    def state(j): return f'({stem}State_{j} init)'
    def theorem(name, args, proof):
        names.append(name)
        lines.extend([f'theorem {name} {args} := {proof}', f'#print axioms {name}'])
    advance = f'(fun row s => stepWithInputs {label}Graph ({label}Scope row.1) ({label}Peers row.1) s row.1 row.2)'
    args = f'(init : Store) (hInitShapes : {stem}InitShapes init)'
    goal = ' ∧ '.join(f'(init {p["tid"]}).shape = {p["shape"]}' for p in initial.values()) or 'True'
    definition(f'def {stem}InitShapes (init : Store) : Prop := {goal}')
    definition(f'def {stem}State_0 (init : Store) : Store := {initial_store}')
    hs = [f'h{q}' for q in range(len(initial))]
    destruct = f'  rcases hInitShapes with ⟨{", ".join(hs)}⟩\n' if len(hs)>1 else ('  have h0 := hInitShapes\n' if hs else '')
    for q, (tid, p) in enumerate(initial.items()):
        name = f'{stem}InitialShape_{q}'
        theorem(name, f'{args} : (init {tid}).shape = {p["shape"]}', 'by\n'+destruct+f'  exact h{q}')
        shape_proofs[tid] = f'{name} init hInitShapes'
        if seeds is not None:
            read = f'{stem}InitialRead_{q}'
            theorem(read, f'(init : Store) : {state(0)} {tid} = init {tid}',
                f'{label}InitialWithSeeds_frame init {tid} (by decide)')
            initial_reads[tid] = f'{read} init'
            group()
    for tid, q in seed_ids.items():
        initial_reads[tid] = f'{label}InitialWithSeeds_seed_{q} init'
    group()
    for j, row in enumerate(rows):
        i, op, ins, outs, scope = (row[k] for k in ('index','op','ins','outs','scope'))
        node = f'{label}Node_{i}'; prev = state(j); nxt = state(j+1)
        reads = []
        for p, t in enumerate(ins):
            name = f'{stem}Read_{j}_{p}'; reads.append(f'{name} init')
            stop = writers[t.tid][0] + 1 if t.tid in writers else 0
            proof = 'by\n' + ''.join(
                f'  rw [{stem}Skip_{q} init {t.tid} (by decide)]\n'
                for q in range(j - 1, stop - 1, -1))
            proof += (f'  exact {writers[t.tid][1]} init' if t.tid in writers else
                      f'  exact {initial_reads[t.tid]}' if seeds is not None else '  rfl')
            theorem(name, f'(init : Store) : {prev} {t.tid} = {values[t.tid]}', proof)
        v = [values[t.tid] for t in ins]; actual = [f'({prev} {t.tid})' for t in ins]
        def expressions(xs):
            if op == 'DATALOADER': return [f'{node}_port{p["port"]}' for p in feeds[i]['ports']]
            if op == 'FW_embedding': return [f'fw_embedding {xs[0]} {xs[1]}']
            if op == 'AllReducePrim': return [f'allReducePrim {len(scope.ranks)} {scope.local_index} [{", ".join(xs)}]']
            if op == 'ReduceScatterPrim': return [f'reduceScatterPrimDimN {scope.params[0]} {len(scope.ranks)} {scope.local_index} [{", ".join(xs)}]']
            if op == 'AllGatherPrim': return [f'allGatherPrimDimN {scope.params[0]} {len(scope.ranks)} {scope.local_index} [{", ".join(xs)}]']
            if op in ('FW_view', 'FW_reshape'): return [f'fw_view {row["params"]} {xs[0]}']
            if op == 'FW_transpose': return [f'transposeAxes {row["params"][0]} {row["params"][1]} {xs[0]}']
            if op == 'FW_matmul': return [f'fw_matmul {xs[0]} {xs[1]}']
            if op == 'FW_div': return [f'fw_div (({row["params"][0]} : Nat) : Scalar) {xs[0]}']
            if op == 'BW_sum': return [f'bw_sum {xs[0]} {xs[1]}']
            if op == 'FW_sum': return [f'fw_sum {xs[0]}']
            # Tensor has no storage/stride fields: contiguous is value identity.
            if op == 'FW_contiguous': return [xs[0]]
            if op == 'FW_gelu': return [f'fw_gelu {xs[0]}']
            if op == 'FW_softmax': return [f'fw_softmax {xs[0]}']
            if op == 'FW_linear': return [f'fw_linear {xs[0]} {xs[1]}']
            if op == 'FW_layernorm': return [f'fw_layernorm {xs[0]} {xs[1]} {xs[2]}']
            if op == 'ChunkPrim': return [f'chunkPrimDimN {scope.dim} {len(scope.ranks)} {scope.local_index} {xs[0]}']
            if op == 'AllToAllPrim': return [f'AllToAllSourceFaithful.tensor {len(scope.ranks)} {scope.local_index} {scope.params[0]} {scope.params[1]} [{", ".join(xs)}]']
            if op == 'FW_add': return [xs[0] if len(xs)==1 else f'elemwiseAdd {xs[0]} {xs[1]}']
            return [xs[0]] * len(outs)
        pure, computed = expressions(v), expressions(actual)
        for p, value in enumerate(pure):
            definition(f'def {stem}Value_{j}_{p} (init : Store) : Tensor := {value}')
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
        elif op in ('ChunkPrim', 'AllGatherPrim', 'ReduceScatterPrim', 'AllReducePrim'):
            rs = list(scope.ranks)
            proof = (f'by\n  change GroupScopedEval.step {label}Graph (.group (some {rs})) {prev} {node} = _\n'
                     f'  rw [GroupScopedEval.step_scoped _ _ _ {rs} (by decide) (by rfl)]\n  rfl')
        else:
            proof = 'by\n  change some (applyNode _ _ _) = _\n  rfl'
        definition(f'def {stem}State_{j+1} (init : Store) : Store := {update}')
        condition = op == 'AllToAllPrim'
        theorem(f'{stem}Step_{j}', f'{args if condition else "(init : Store)"} : stepWithInputs {label}Graph ({label}Scope {node}) ({label}Peers {node}) {prev} {node} {feed} = some {nxt}', proof)
        steps.append(f'{stem}Step_{j} init'+(' hInitShapes' if condition else ''))
        pairs = '[' + ', '.join(f'({t.tid}, {value})' for t, value in zip(outs, computed)) + ']'
        theorem(f'{stem}Skip_{j}',
                f'(init : Store) (tid : Tid) (h : tid ∉ {[t.tid for t in outs]}) : {nxt} tid = {prev} tid',
                f'by\n  change storeSet {prev} {pairs} tid = {prev} tid\n'
                f'  exact storeSet_eq_of_not_mem_fst _ _ _ (by simpa only [List.map] using h)')
        input_shapes = [shape_proofs[t.tid] for t in ins]
        for p, (t, value, sh) in enumerate(zip(outs, computed, row['output_shapes'])):
            vn = f'{stem}Value_{j}_{p}'; on = f'{stem}Written_{j}_{p}'; sn = f'{stem}Shape_{j}_{p}'
            theorem(on, f'(init : Store) : {nxt} {t.tid} = {vn} init',
                    f'by\n  change {value} = {vn} init\n  simp only [{vn}'+(', '+', '.join(reads) if reads else '')+']')
            # Project shape through this operator only. Never simplify a nested
            # value graph: real-width normalization/linear arithmetic is costly
            # even though it is irrelevant to this theorem.
            shape_start = f'by\n  unfold {vn}\n'
            if op in ('FW_view', 'FW_reshape', 'FW_sum'):
                shape_proof = '  rfl'
            elif op == 'BW_sum':
                shape_proof = f'  exact {input_shapes[1]}'
            elif op == 'FW_transpose':
                shape_proof = ('  change listSwapAt _ _ _ = _\n'
                               f'  rw [{input_shapes[0]}]\n  rfl')
            elif op == 'FW_matmul':
                shape_proof = ('  unfold fw_matmul batchedMatmul\n'
                               f'  rw [{input_shapes[0]}, {input_shapes[1]}]\n  rfl')
            elif op in ('FW_div', 'FW_contiguous', 'FW_gelu'):
                shape_proof = f'  exact {input_shapes[0]}'
            elif op == 'FW_softmax':
                shape_proof = ('  unfold fw_softmax softmax\n'
                               f'  split <;> exact {input_shapes[0]}')
            elif op == 'FW_layernorm':
                shape_proof = ('  rw [SourceScopedPrefix.layernorm_shape]\n'
                               f'  exact {input_shapes[0]}')
            elif op == 'FW_linear':
                dims = row['input_shapes'][0] + [row['input_shapes'][1][0]]
                lemma = 'fw_linear_3d_shape' if len(dims) == 4 else 'SourceScopedPrefix.linear_shape_2d'
                shape_proof = f'  exact {lemma} {" ".join(map(str, dims))} {" ".join(v)} ' + ' '.join(f'({h})' for h in input_shapes)
            elif op == 'AllReducePrim':
                shape_proof = (f'  rw [allReducePrim_shape _ _ _ {v[0]} rfl]\n'
                               f'  exact {input_shapes[0]}')
            elif op == 'AllGatherPrim':
                dim, = scope.params
                shape_proof = (f'  exact allGatherPrimDimN_shape {dim} {len(scope.ranks)} '
                               f'[{", ".join(v)}] {row["input_shapes"][0]} ({input_shapes[0]})')
            elif op == 'ReduceScatterPrim':
                shape_proof = (f'  unfold reduceScatterPrimDimN\n'
                               f'  apply chunkPrimDimN_shape {scope.params[0]} {len(scope.ranks)} '
                               f'{scope.local_index} _ {row["input_shapes"][0]}\n'
                               f'  · rw [allReducePrim_shape _ _ _ {v[0]} rfl]\n'
                               f'    exact {input_shapes[0]}\n'
                               f'  · decide')
            elif op == 'ChunkPrim':
                shape_proof = (f'  exact chunkPrimDimN_shape {scope.dim} {len(scope.ranks)} '
                               f'{scope.local_index} {v[0]} {row["input_shapes"][0]} '
                               f'({input_shapes[0]}) (by decide)')
            elif op == 'FW_multiref' or (op == 'FW_add' and len(ins) == 1):
                shape_proof = f'  exact {input_shapes[0]}'
            else:
                shape_defs = []
                if op == 'DATALOADER':
                    shape_defs += [f'{node}_port{p}', 'Tensor.mkShape']
                elif op == 'FW_embedding':
                    shape_defs += ['fw_embedding_shape', 'lastD'] + input_shapes
                elif op == 'FW_add':
                    shape_defs += ['elemwiseAdd', 'Tensor.mkShape', 'outShape2'] + input_shapes
                elif op == 'AllToAllPrim':
                    shape_start += '  rw [AllToAllSourceFaithful.tensor_shape _ _ _ _ _ _ (by decide)]\n'
                    shape_defs = input_shapes[:1]
                shape_proof = '  simp [' + ', '.join(shape_defs) + ']'
            theorem(sn, f'{args} : ({vn} init).shape = {sh}', shape_start + shape_proof)
            # Later proof elaboration must use the named read/shape facts, not
            # recursively evaluate normalization or matrix entries. Local only:
            # the generated value definitions and exported statements are unchanged.
            lines.append(f'attribute [local irreducible] {vn}')
            opaque.append(vn)
            values[t.tid] = f'({vn} init)'; writers[t.tid] = (j, on); shape_proofs[t.tid] = f'{sn} init hInitShapes'
        lines.append(f'attribute [local irreducible] {stem}State_{j+1}')
        opaque.append(f'{stem}State_{j+1}')
        group()
    selected = [r['index'] for r in rows]; length = len(rows); final = state(length)
    # Certificates share the exact existing computed Store endpoints.  Their
    # request lists are proof-only; the canonical graph and schedule stay intact.
    # A balanced append tree bounds assembly without re-expanding earlier runs.
    def requests(a, b): return f'{stem}Requests_{a}_{b}'
    def run_name(a, b): return f'{stem}Run_{a}_{b}'
    def interval(a, b):
        req = requests(a, b)
        if b - a <= RUN_STEP_BUDGET:
            items = ', '.join(f'({label}Node_{i}, ' +
                (f'some {label}Node_{i}_feed' if i in feeds else 'none') + ')'
                for i in selected[a:b])
            definition(f'def {req} : List InputRequest := [{items}]')
            proof = f'by\n  simp only [{req}, runUsing, List.foldl_cons, List.foldl_nil, Option.bind_some]\n'
            proof += '\n'.join(f'  rw [{steps[q]}]' +
                ('\n  simp only [Option.bind_some]' if q < b-1 else '') for q in range(a, b))
            if a == b:
                proof = f'by\n  rfl'
        else:
            middle = a + (b - a) // 2
            interval(a, middle); interval(middle, b)
            definition(f'def {req} : List InputRequest := {requests(a, middle)} ++ {requests(middle, b)}')
            proof = (f'by\n  unfold {req}\n'
                     f'  rw [SourceScopedPrefix.runUsing_append, {run_name(a, middle)} init hInitShapes]\n'
                     f'  exact {run_name(middle, b)} init hInitShapes')
        theorem(run_name(a, b), f'{args} : runUsing {advance} {req} (some {state(a)}) = some {state(b)}', proof)
        group()
    if RUN_STEP_BUDGET < 1:
        raise ValueError('run step budget must be positive')
    interval(0, length)
    theorem(stem+'RequestsCoverage',
            f': {label}InputRequests.take {length} = {requests(0, length)}', 'by\n  rfl')
    group()
    run = f'runUsing {advance} ({label}InputRequests.take {length}) (some {initial_store})'
    theorem(stem+'Success', f'{args} : {run} = some {final}',
            f'by\n  rw [{stem}RequestsCoverage]\n  exact {run_name(0, length)} init hInitShapes')
    out = rows[-1]['outs'][-1]; sh = shapes_out = rows[-1]['output_shapes'][-1]
    theorem(stem+'Output', f'(init : Store) : {final} {out.tid} = {values[out.tid]}', f'{writers[out.tid][1]} init')
    theorem(stem+'OutputShape', f'{args} : ({final} {out.tid}).shape = {sh}', f'by\n  rw [{stem}Output]\n  exact {shape_proofs[out.tid]}')
    theorem(stem+'Frame', f'{args} (tid : Tid) (ht : ∀ row ∈ {label}InputRequests.take {length}, tid ∉ row.1.outs) : {final} tid = {initial_store} tid',
            f'SourceScopedPrefix.frame {label}Graph {label}Scope {label}Peers _ {initial_store} {final} tid ht ({stem}Success init hInitShapes)')
    denote = label + ('DenoteWithInputs' if seeds is None else 'SeededDenoteWithInputs')
    entry_unfold = '' if seeds is None else f'  unfold {label}SeededDenoteWithInputs\n'
    theorem(stem+'Continuation', f'{args} : {denote} init = runUsing {advance} ({label}InputRequests.drop {length}) (some {final})',
            f'by\n{entry_unfold}  rw [{label}DenoteWithInputs_entry]\n  exact SourceScopedPrefix.continuation _ _ {length} {initial_store} {final} ({stem}Success init hInitShapes)')
    group(final=True)
    text = groups if structured else _HEADER + '\n'.join(g.text for g in groups) + _FOOTER
    return text, dict(status='conditional-prefix-emitted', prefix_nodes=selected,
        prefix_length=length, boundary_index=guards[-1]['index'], guards=guards, frontier=frontier,
        initial_premises=list(initial.values()), output_tid=out.tid, output_shape=shapes_out,
        kernel_checks=names, kernel_checked=False, whole_world_option_success=False, external_adapter_proved=False)
