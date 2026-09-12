"""Original dV -> inverse layouts -> V linear, in one successful final Store.

The roots import the original matmul/ReduceScatter equations. Only this path's
new source readers are emitted. Named values share the expression DAG; no
cross-world gradient equality or Torch/kernel certification is claimed here.
"""
from copy import copy

from Verdict import graph_to_lean as compiler
from Verdict import runtime_backward_collective_reads as collective
from Verdict import runtime_backward_linear_reads as linear
from Verdict import runtime_backward_matmul_reads as matmul
from Verdict import runtime_backward_matmul_reduce_scatter_consumers as previous
from Verdict import runtime_backward_transpose_reads as transpose
from Verdict import runtime_backward_view_reads as inverse_view
from Verdict.runtime_lineage import _same_typed

_FLAGS = ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement')


def _require(condition, reason):
    if not condition:
        raise ValueError('bw-v-projection ' + reason)


def _consumer(view, cells, order, producer_index, port, opname):
    """Select a same-rank consumer by the complete original output identity."""
    producer = cells[producer_index]
    _require(type(port) is int and 0 <= port < len(producer.outputs), 'invalid output port')
    ref = tuple(producer.outputs[port])
    matches = [(i, c) for i, c in enumerate(cells)
               if c.rank == producer.rank and any(_same_typed(tuple(r), ref) for r in c.inputs)]
    _require(len(matches) == 1 and matches[0][1].opname.name == opname,
             'unique original ' + opname + ' consumer required')
    index, cell = matches[0]
    inputs = view.node_inputs(cell.node)
    output = view.node_outputs(producer.node)[port]
    ports = [j for j, r in enumerate(cell.inputs) if _same_typed(tuple(r), ref)]
    _require(len(ports) == 1 and (opname in ('ReduceScatterPrim', 'AllToAllPrim', 'AllGatherPrim')
                                or ports == [0]), 'original cotangent input port mismatch')
    target = inputs[ports[0]]
    _require(_same_typed(tuple(view.source_tensor(output)), ref)
             and _same_typed(tuple(view.source_tensor(target)), ref)
             and _same_typed(target.tid, output.tid), 'original fullref/lowered edge mismatch')
    _require(order['execution_to_source'].index(producer_index)
             < order['execution_to_source'].index(index), 'original edge execution order mismatch')
    return index


def discover(worlds):
    """Discover before rendering: not source adjacency, nor a shape-based join."""
    _require([w[-1] for w in worlds] == ['sm', 'pm'], 'original SM/PM worlds required')
    paths = []
    for view, cells, _, order, label in worlds:
        ops = (['BW_transpose', 'BW_view', 'BW_linear'] if label == 'sm' else
               ['ReduceScatterPrim', 'BW_transpose', 'AllToAllPrim', 'BW_view', 'AllGatherPrim', 'BW_linear'])
        for rank in dict.fromkeys(c.rank for c in cells):
            indices = [i for i, c in enumerate(cells) if c.rank == rank and c.opname.name == 'BW_matmul']
            _require(bool(indices), 'original dV matmul root missing')
            root = indices[0]
            path, port = [root], 1  # dY of this matmul is dV, never parameter dW.
            for op in ops:
                path.append(_consumer(view, cells, order, path[-1], port, op))
                port = 0
            paths.append(dict(world=label, rank=rank, matmul_index=root, source_indices=path))
    return paths


def _parameter_role(cell):
    # Preserve the raw source distinction: bw_linear's .2 alone is not proof
    # that a saved weight is a trainable parameter (nor is matmul's .2).
    return 'parameter_gradient' if cell._input_irs[2].is_param() is True else 'weight_gradient'


def _collective_parents(raw, values):
    """Join ordered, authenticated peer reads to already certified DAG stages."""
    parents = []
    for peer in raw['predecessors']:
        key = (raw['world'], peer['source_index'])
        _require(key in values, 'certified peer DAG stage missing')
        certified = values[key]
        _require(_same_typed(certified['source_read'], peer), 'certified original peer read mismatch')
        parents.append(certified)
    _require(_same_typed([r['output_tids'][0] for r in parents], raw['input_tids'])
             and _same_typed([r['output_refs'][0] for r in parents], raw['input_refs'])
             and all(r['execution_index'] < raw['execution_index'] for r in parents),
             'ordered collective DAG edge mismatch')
    return parents


def render(worlds, capture_path, rank_code_directory):
    paths = discover(worlds)
    _, prior = previous.render(worlds, capture_path, rank_code_directory)
    pm_roots = {r['source_index']: r for r in prior['reads']}
    _require(set(pm_roots) == {p['source_indices'][1] for p in paths if p['world'] == 'pm'},
             'original ReduceScatter root inventory mismatch')
    fresh = compiler._load_chunk_source(capture_path, rank_code_directory)
    contexts = {}
    for view, cells, snapshot, order, label in worlds:
        if label == 'pm':
            view = copy(view)
            compiler.attach_collective_scopes(view, fresh)
            snapshot = fresh
        contexts[label] = (view, cells, snapshot, order, label)

    proofs, rows, values = [], [], {}
    sources = {kind: [] for kind in ('transpose', 'view', 'collective', 'linear')}

    def emit(raw, expressions, parents, roles, *, source_names=None, is_collective=False, pair=False):
        label, index = raw['world'], raw['source_index']
        name = f'backwardVValue_{label}_{index}'
        tids = raw['output_tids']
        value_type = 'Tensor × Tensor' if pair else 'Tensor'
        body = expressions[0]
        proofs.extend([f'def {name} (t : Store) : {value_type} :=', f'  {body}'])
        names = []
        expressions_out = []
        for port, tid in enumerate(tids):
            suffix = ('dx', 'dw')[port] if pair else 'dv'
            theorem = f'{name}_{suffix}_sameStore'
            rhs = f'({name} t).{port+1}' if pair else f'{name} t'
            expanded = f'({body}).{port+1}' if pair else body
            proofs.extend([f'theorem {theorem} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
                           f'    t {tid} = {rhs} := by', f'  change t {tid} = {expanded}',
                           f'  rw [{(source_names or raw["theorems"])[port]} s t h]'])
            if is_collective:
                proofs.append('  simp only [List.map_cons, List.map_nil]')
            if parents:
                proofs.append('  rw [' + ', '.join(p['composition_theorems'][0] + ' s t h' for p in parents) + ']')
            proofs.append(f'#print axioms {theorem}')
            names.append(theorem)
            expressions_out.append(rhs)
        row = dict(raw, value_name=name, value_body=body, value_expressions=expressions_out,
                   composition_theorems=names, output_roles=roles,
                   parents=[dict(world=p['world'], source_index=p['source_index'],
                                 output_tid=p['output_tids'][0], output_ref=p['output_refs'][0],
                                 value_name=p['value_name'], theorem=p['composition_theorems'][0]) for p in parents])
        rows.append(row)
        _require((label, index) not in values, 'duplicate DAG stage')
        values[label, index] = row
        return row

    # Imported roots: no regeneration/emission of the preceding whole prefix.
    for p in paths:
        label = p['world']
        if label == 'sm':
            view, cells, snapshot, order, _ = contexts[label]
            _, raw = matmul.render_read(view, cells, snapshot, p['matmul_index'], order, label)
            body = '(bw_matmul ' + ' '.join(f'(t {tid})' for tid in raw['input_tids']) + ').2'
            root = dict(raw, output_tids=[raw['output_tids'][1]], output_refs=[raw['output_refs'][1]],
                        selected_output_port=1, stage='matmul_dv')
            emit(root, [body], [], ['value_cotangent'], source_names=[raw['theorems'][1]])
        else:
            raw = pm_roots[p['source_indices'][1]]
            root = dict(raw, output_tids=[raw['output_tid']], output_refs=[raw['output_ref']],
                        selected_output_port=0, stage='reduced_dv')
            emit(root, [raw['expression']], [], ['value_cotangent'], source_names=[raw['composition_theorem']])

    # Wave ordering keeps every peer value/theorem defined before its exchange.
    stages = [('BW_transpose', 'transpose', transpose), ('AllToAllPrim', 'collective', transpose),
              ('BW_view', 'view', inverse_view), ('AllGatherPrim', 'collective', inverse_view),
              ('BW_linear', 'linear', linear)]
    for opname, kind, reader in stages:
        for p in paths:
            label = p['world']
            view, cells, snapshot, order, _ = contexts[label]
            indices = p['source_indices']
            selected = [i for i in indices if cells[i].opname.name == opname]
            if not selected:
                continue  # SM has no AA/AG.
            index, = selected
            prev_index = indices[indices.index(index)-1]
            parent = values[label, prev_index]
            if kind == 'collective':
                text, raw = collective.render_read(view, cells, snapshot, index, order, label, reader.render_read, 0)
                parents = _collective_parents(raw, values)
                args = ', '.join(f'{r["value_name"]} t' for r in parents)
                n, local = len(raw['ranks']), raw['local_index']
                if opname == 'AllToAllPrim':
                    idim, odim = raw['params']
                    body = f'AllToAllSourceFaithful.tensor {n} {local} {idim} {odim} [{args}]'
                else:
                    dim, = raw['params']
                    body = f'allGatherPrimDimN {dim} {n} {local} [{args}]'
                normalized = dict(raw, output_tids=[raw['output_tid']], output_refs=[raw['output_ref']], stage=opname)
                emit(normalized, [body], parents, ['value_cotangent'], is_collective=True)
            else:
                text, raw = reader.render_read(view, cells, snapshot, index, order, label)
                _require(_same_typed(parent['output_refs'][0], raw['input_refs'][0])
                         and _same_typed(parent['output_tids'][0], raw['input_tids'][0])
                         and parent['execution_index'] < raw['execution_index'], 'certified cotangent DAG edge mismatch')
                raw = dict(raw, source_read=raw, stage=opname,
                           input_shapes=[list(view.tensor_shape(t)) for t in view.node_inputs(cells[index].node)])
                value = f'({parent["value_name"]} t)'
                if opname == 'BW_transpose':
                    a, b = raw['params']
                    body = f'transposeAxes {a} {b} {value}'
                elif opname == 'BW_view':
                    body = f'fw_view {raw["params"]} {value}'
                else:
                    _, x, weight = raw['input_tids']
                    body = f'bw_linear {value} (t {x}) (t {weight})'
                roles = ['input_gradient', _parameter_role(cells[index])] if kind == 'linear' else ['value_cotangent']
                emit(raw, [body], [parent], roles, pair=kind == 'linear')
            sources[kind].append(text)
    return '\n'.join(proofs) + '\n', dict(
        reads=rows, paths=paths, linear_reads=[r for r in rows if r['stage'] == 'BW_linear'],
        **{kind + '_source': ''.join(text) for kind, text in sources.items()},
        **{flag: False for flag in _FLAGS})
