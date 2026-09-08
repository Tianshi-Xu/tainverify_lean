"""Portable production option/seeded emitter contracts."""
import inspect
import unittest
from Verdict import runtime_input_feed as feed, runtime_seed_feed as seed
from Verdict import runtime_prefix as prefix
from math import prod
from scripts.tests.test_runtime_seed_feed import fixture


def linear_world(root, k, ndim=3, fault=None, *, layernorm=False, elementwise=None, multiref=None, repeated=False, inverse=None, layout=None, matmul=None, matmul_batch=None, softmax=None, softmax_dim=-1):
    """Real raw/source/feed fixture; mock only portable seed authentication."""
    from types import SimpleNamespace as NS
    from unittest.mock import patch
    from scripts.tests.test_runtime_scoped_prefix import collective_world
    from scripts.tests.test_graph_to_lean_runtime_lineage import T, N, IR
    fields = ('world', 'runtime_rank', 'microbatch', 'source_tid', 'version')
    def transform(sm, pm):
        grads = []
        def ordinary(graph, rank, cid, op, inputs, shapes, kwargs=None):
            label = 'p' if graph is pm else 's'
            outputs = [T(label, rank, 0, cid+p, 1) for p in range(len(shapes))]
            node = NS(node=N(label, rank, 0, cid, op), rank=rank, opname=op,
                kwargs={} if kwargs is None else kwargs, inputs=inputs, outputs=outputs,
                _input_irs=[IR(t.tid, 'activation', graph.shapes[t]) for t in inputs],
                _output_irs=[IR(t.tid, 'gradient', sh) for t, sh in zip(outputs, shapes)])
            graph.shapes.update(dict(zip(outputs, shapes))); graph.cells.append(node)
            return node
        for graph in (sm, pm):
            sources = [c for c in graph.cells if c.opname == ('FW_linear' if graph is pm else 'FW_embedding')]
            for src in sources:
                rank = src.rank
                if graph is pm and ndim == 2:
                    x = src.inputs[0]; sh = (2*k, 3)
                    v = ordinary(graph, rank, 800, 'FW_view', [x], [sh], {'size': sh})
                    graph.cells.remove(v); graph.cells.insert(graph.cells.index(src), v)
                    src.inputs[0] = v.outputs[0]; src._input_irs[0] = v._output_irs[0]
                    graph.shapes[src.outputs[0]] = (2*k, 5)
                    src._output_irs[0] = IR(src.outputs[0].tid, 'projection', (2*k, 5))
                y = src.outputs[0]; g = T('p' if graph is pm else 's', rank, 0, 900, 0)
                graph.shapes[g] = (1,)
                s = ordinary(graph, rank, 901, 'BW_sum', [g, y], [graph.shapes[y]])
                s._input_irs[0].is_grad = lambda: True
                if graph is sm: continue
                dy, x, w = s.outputs[0], *src.inputs
                if fault in ('grad-batch', 'grad-width', 'x-width', 'weight-dims'):
                    t = dy if fault.startswith('grad') else x if fault == 'x-width' else w
                    sh = list(graph.shapes[t])
                    if fault == 'grad-batch': sh = [sh[0]*sh[1], 1, sh[2]] if ndim == 3 else [1, sh[0]*sh[1]]
                    else: sh[-2], sh[-1] = sh[-1], sh[-2]
                    v = ordinary(graph, rank, 910, 'FW_view', [t], [tuple(sh)], {'size': tuple(sh)})
                    if fault.startswith('grad'): dy = v.outputs[0]
                    elif fault == 'x-width': x = v.outputs[0]
                    else: w = v.outputs[0]
                bw = ordinary(graph, rank, 920, 'BW_linear', [dy, x, w],
                    [graph.shapes[src.inputs[0]], graph.shapes[src.inputs[1]]], {'bias': None})
                if fault == 'bias': bw.kwargs['bias'] = True
                elif fault == 'params': bw.kwargs['unknown'] = 1
                elif fault == 'arity': bw.inputs.pop(); bw._input_irs.pop()
                elif fault == 'outputs': bw.outputs.pop(); bw._output_irs.pop()
                elif fault in ('dx-shape', 'dw-shape'):
                    port = int(fault == 'dw-shape'); t = bw.outputs[port]
                    graph.shapes[t] = (7,); bw._output_irs[port] = IR(t.tid, 'gradient', (7,))
                if layernorm:
                    ln = next(c for c in graph.cells if c.rank == rank and c.opname == 'FW_layernorm')
                    x, gamma, beta = ln.inputs
                    if ndim == 2:
                        x = ordinary(graph, rank, 925, 'FW_view', [x], [(2*k, 3)], {'size': (2*k, 3)}).outputs[0]
                    inputs = [bw.outputs[0], x, gamma, beta]
                    if fault in ('dy-shape', 'x-shape', 'gamma-shape', 'beta-shape'):
                        port = ('dy-shape', 'x-shape', 'gamma-shape', 'beta-shape').index(fault)
                        t = inputs[port]; sh = tuple(reversed(graph.shapes[t])) if port < 2 else (1, 3)
                        inputs[port] = ordinary(graph, rank, 926, 'FW_view', [t], [sh], {'size': sh}).outputs[0]
                    kw = dict(normalized_shape=(3,), eps=1e-5)
                    if fault == 'epsilon': kw['eps'] = 1e-4
                    if fault == 'normalized-shape': kw['normalized_shape'] = (2*k, 3)
                    if fault == 'ln-params': kw['unknown'] = 1
                    lnback = ordinary(graph, rank, 930, 'BW_layernorm', inputs,
                        [graph.shapes[x], (3,), (3,)], kw)
                    if fault == 'ln-arity': lnback.inputs.pop(); lnback._input_irs.pop()
                    if fault == 'ln-outputs': lnback.outputs.pop(); lnback._output_irs.pop()
                    if fault == 'duplicate-outputs': lnback.outputs[2] = lnback.outputs[1]
                    if fault in ('ln-dx', 'ln-dgamma', 'ln-dbeta'):
                        port = ('ln-dx', 'ln-dgamma', 'ln-dbeta').index(fault)
                        t = lnback.outputs[port]; graph.shapes[t] = (7,)
                        lnback._output_irs[port] = IR(t.tid, 'gradient', (7,))
                    if elementwise:
                        y = x if elementwise == 'equal' else gamma
                        addins = [lnback.outputs[0], x, y]
                        if fault == 'add-dy': addins[0] = gamma
                        if fault == 'add-broadcast':
                            addins[2] = ordinary(graph, rank, 933, 'FW_view', [x], [(3, 2*k)], {'size': (3, 2*k)}).outputs[0]
                        add = ordinary(graph, rank, 935, 'BW_add', addins,
                            [graph.shapes[x], graph.shapes[y]], {'alpha': 1})
                        if fault == 'add-alpha': add.kwargs['alpha'] = 2
                        if fault == 'add-params': add.kwargs['unknown'] = 1
                        if fault == 'add-arity': add.inputs.pop(); add._input_irs.pop()
                        if fault == 'add-outputs': add.outputs.pop(); add._output_irs.pop()
                        if fault == 'add-duplicate': add.outputs[1] = add.outputs[0]
                        if fault in ('add-dx', 'add-dyout'):
                            port = int(fault == 'add-dyout'); t = add.outputs[port]
                            graph.shapes[t] = (7,); add._output_irs[port] = IR(t.tid, 'gradient', (7,))
                        geluins = [add.outputs[0], x]
                        if fault == 'gelu-dy': geluins[0] = gamma
                        gelu = ordinary(graph, rank, 938, 'BW_gelu', geluins, [graph.shapes[x]], {'approximate': 'none'})
                        if fault == 'gelu-approx': gelu.kwargs['approximate'] = 'tanh'
                        if fault == 'gelu-params': gelu.kwargs['unknown'] = 1
                        if fault == 'gelu-arity': gelu.inputs.pop(); gelu._input_irs.pop()
                        if fault == 'gelu-output':
                            t = gelu.outputs[0]; graph.shapes[t] = (7,); gelu._output_irs[0] = IR(t.tid, 'gradient', (7,))
                        ordinary(graph, rank, 960, 'BW_gelu', [add.outputs[-1], y], [graph.shapes[y]], {'approximate': 'none'})
                    else:
                        ordinary(graph, rank, 935, 'BW_view', [lnback.outputs[0]], [graph.shapes[x]], {'size': graph.shapes[x]})
                if inverse:
                    op, request, shape = inverse
                    original = ordinary(graph, rank, 965, 'FW_view', [x], [shape], {'size': shape}).outputs[0]
                    back = ordinary(graph, rank, 970, op, [bw.outputs[0], original], [shape], request)
                    if fault == 'inverse-initial':
                        back.inputs = [w, w]
                        back._input_irs = [src._input_irs[1], src._input_irs[1]]
                        back.kwargs = {'size': graph.shapes[w]}
                        graph.shapes[back.outputs[0]] = graph.shapes[w]
                        back._output_irs = [IR(back.outputs[0].tid, 'gradient', graph.shapes[w])]
                    if fault == 'inverse-arity': back.inputs.pop(); back._input_irs.pop()
                    if fault == 'inverse-outputs': back.outputs.append(back.outputs[0]); back._output_irs.append(back._output_irs[0])
                    if fault == 'inverse-output':
                        graph.shapes[back.outputs[0]] = (2*k, 3)
                        back._output_irs = [IR(back.outputs[0].tid, 'gradient', (2*k, 3))]
                    if fault == 'inverse-product':
                        back.inputs[0] = dy; back._input_irs[0] = s._output_irs[0]
                    ordinary(graph, rank, 975, 'BW_contiguous', [back.outputs[0], original], [shape])
                if layout:
                    op, request, shape = layout
                    original = ordinary(graph, rank, 976, 'FW_view', [x], [shape], {'size': shape}).outputs[0]
                    gradshape = list(shape)
                    if op == 'BW_transpose' and all(type(request.get(key)) is int and -len(shape) <= request[key] < len(shape) for key in ('dim0', 'dim1')):
                        a, b = request['dim0'], request['dim1']
                        gradshape[a], gradshape[b] = gradshape[b], gradshape[a]
                    gradient = ordinary(graph, rank, 977, 'FW_view', [bw.outputs[0]], [tuple(gradshape)], {'size': tuple(gradshape)}).outputs[0]
                    if op == 'BW_transpose':
                        gradient = ordinary(graph, rank, 978, 'BW_contiguous', [gradient, gradient], [tuple(gradshape)]).outputs[0]
                    back = ordinary(graph, rank, 979, op, [gradient, original], [shape], request)
                    if fault == 'layout-arity': back.inputs.pop(); back._input_irs.pop()
                    if fault == 'layout-initial': back.inputs[1] = w; back._input_irs[1] = src._input_irs[1]
                    if fault == 'layout-dy': back.inputs[0] = dy; back._input_irs[0] = s._output_irs[0]
                    if fault == 'layout-output':
                        graph.shapes[back.outputs[0]] = (7,)
                        back._output_irs[0] = IR(back.outputs[0].tid, 'gradient', (7,))
                    ordinary(graph, rank, 981, 'BW_multiref', [back.outputs[0]], [shape])
                if softmax:
                    shape = tuple(softmax)
                    original = ordinary(graph, rank, 982, 'FW_view', [x], [shape], {'size': shape}).outputs[0]
                    forward = ordinary(graph, rank, 983, 'FW_softmax', [original], [shape], {'dim': softmax_dim})
                    gradient = ordinary(graph, rank, 984, 'FW_view', [bw.outputs[0]], [shape], {'size': shape}).outputs[0]
                    operands = [gradient, original]
                    kw = {'dim': softmax_dim, 'dtype': None}
                    if fault in ('softmax-g-uncomputed', 'softmax-x-uncomputed'):
                        operands[int(fault == 'softmax-x-uncomputed')] = g
                    if fault == 'softmax-g-shape': operands[0] = dy
                    if fault == 'softmax-axis': kw['dim'] = -2
                    if fault == 'softmax-axis-oob': kw['dim'] = -len(shape)-1
                    if fault == 'softmax-axis-type': kw['dim'] = -1.0
                    if fault == 'softmax-dtype': kw['dtype'] = 'float32'
                    if fault == 'softmax-kwargs': kw['unknown'] = 1
                    if fault == 'softmax-consts': kw['__consts'] = [1]
                    back = ordinary(graph, rank, 988, 'BW_softmax', operands, [shape], kw)
                    if fault == 'softmax-arity': back.inputs.pop(); back._input_irs.pop()
                    if fault == 'softmax-outputs': back.outputs.append(back.outputs[0]); back._output_irs.append(back._output_irs[0])
                    if fault == 'softmax-output-shape':
                        graph.shapes[back.outputs[0]] = (7,)
                        back._output_irs[0] = IR(back.outputs[0].tid, 'gradient', (7,))
                    ordinary(graph, rank, 994, 'BW_div', [back.outputs[0], original], [shape], {'__consts': [2]})
                if matmul:
                    batch = (1,) * (matmul - 2)
                    shapes = [batch + (2*k, 5), batch + (2*k, 3), batch + (5, 3)]
                    operands = [ordinary(graph, rank, 982+p, 'FW_view', [t], [sh], {'size': sh}).outputs[0]
                                for p, (t, sh) in enumerate(zip((dy, x, w), shapes))]
                    bshape = batch + (3, 5)
                    operands[2] = ordinary(graph, rank, 986, 'FW_transpose', [operands[2]], [bshape],
                                           {'dim0': matmul-2, 'dim1': matmul-1}).outputs[0]
                    if matmul_batch is not None:
                        # Repartition computed activation data into real batches;
                        # compute g too, rather than adding an initial oracle.
                        batch = tuple(matmul_batch)
                        assert len(batch) == matmul-2 and (2*k) % prod(batch) == 0
                        m = 2*k // prod(batch)
                        shapes = [batch + (m, m), batch + (m, 3)]
                        bshape = batch + (3, m)
                        a = ordinary(graph, rank, 985, 'FW_view', [x], [shapes[1]], {'size': shapes[1]}).outputs[0]
                        b = ordinary(graph, rank, 987, 'FW_view', [bw.outputs[0]], [bshape], {'size': bshape}).outputs[0]
                        grad = ordinary(graph, rank, 990, 'FW_matmul', [a, b], [shapes[0]]).outputs[0]
                        operands = [grad, a, b]
                    if fault == 'matmul-broadcast-only':
                        # Legal Torch broadcasting: A/g have batch K, B has 1.
                        # Keeping g's batch equal to A isolates the batch guard.
                        shapes = [(k, 2, 5), (k, 2, 3)]
                        operands[:2] = [ordinary(graph, rank, 985+p*2, 'FW_view', [t], [sh], {'size': sh}).outputs[0]
                                        for p, (t, sh) in enumerate(zip((dy, x), shapes))]
                    if fault in ('matmul-g-shape', 'matmul-contraction', 'matmul-batch', 'matmul-rank'):
                        port = 0 if fault == 'matmul-g-shape' else 2
                        shape = list(graph.shapes[operands[port]])
                        if fault == 'matmul-rank': shape = (prod(shape),)
                        elif fault == 'matmul-batch': shape = (3, 1, 5)
                        else: shape[-2], shape[-1] = shape[-1], shape[-2]
                        operands[port] = ordinary(graph, rank, 987, 'FW_view', [operands[port]],
                            [tuple(shape)], {'size': tuple(shape)}).outputs[0]
                    if fault in ('matmul-g-uncomputed', 'matmul-a-uncomputed', 'matmul-b-uncomputed'):
                        port = {'matmul-g-uncomputed': 0, 'matmul-a-uncomputed': 1, 'matmul-b-uncomputed': 2}[fault]
                        operands[port] = g
                    back = ordinary(graph, rank, 988, 'BW_matmul', operands.copy(), [shapes[1], bshape])
                    if fault == 'matmul-input-arity': back.inputs.pop(); back._input_irs.pop()
                    elif fault == 'matmul-output-arity': back.outputs.append(back.outputs[0]); back._output_irs.append(back._output_irs[0])
                    elif fault == 'matmul-duplicate': back.outputs[1] = back.outputs[0]
                    elif fault == 'matmul-params': back.kwargs['unknown'] = 1
                    elif fault == 'matmul-output-shape':
                        graph.shapes[back.outputs[1]] = (7,)
                        back._output_irs[1] = IR(back.outputs[1].tid, 'gradient', (7,))
                    ordinary(graph, rank, 991, 'BW_contiguous', [back.outputs[0], operands[1]], [shapes[1]])
                    ordinary(graph, rank, 992, 'BW_contiguous', [back.outputs[1], operands[2]], [bshape])
                    ordinary(graph, rank, 994, 'BW_multiref', [back.outputs[0]], [shapes[1]])
                grads.append(bw)
        if elementwise:
            t = grads[0].outputs[0]; sh = pm.shapes[t]
            if multiref is not None:
                branches = [ordinary(pm, 0, 980+q, 'FW_div', [t], [sh], {'__consts': [q+1]}).outputs[0]
                            for q in range(multiref)]
                branches.reverse()
                if repeated and branches: branches[-1] = branches[0]
                if fault == 'multiref-shape' and branches:
                    branches[-1] = ordinary(pm, 0, 990, 'FW_view', [t], [tuple(reversed(sh))], {'size': tuple(reversed(sh))}).outputs[0]
                if fault == 'multiref-uncomputed': branches[0] = next(c.inputs[0] for c in pm.cells if c.opname == 'BW_sum')
                kw = {'times': multiref} if fault == 'multiref-times' else {'unknown': 1} if fault == 'multiref-params' else {'__consts': [2]} if fault == 'multiref-consts' else {}
                outs = [sh, sh] if fault == 'multiref-outputs' else [(7,)] if fault == 'multiref-output-shape' else [sh]
                merged = ordinary(pm, 0, 995, 'BW_multiref', branches, outs, kw)
                t = merged.outputs[0]
            ordinary(pm, 0, 997, 'BW_view', [t], [pm.shapes[t]], {'size': pm.shapes[t]})
        if fault: return
        for rank in range(k):
            inputs = [g.outputs[0] for g in grads]
            sh = list(pm.shapes[inputs[0]]); dim = ndim-2; sh[dim] //= k
            t = T('p', rank, 0, 940, 1); pm.shapes[t] = tuple(sh)
            pm.cells.append(NS(node=N('p', rank, 0, 940, 'ReduceScatterAllGatherPrim'), rank=rank,
                opname='ReduceScatterPrim', kwargs={'ranks': list(range(k)), 'dim': dim}, inputs=inputs, outputs=[t]))
            ordinary(pm, rank, 950, 'BW_layernorm', [t], [tuple(sh)])
    def inventory(config, sm, pm, raw_sm, raw_pm, root):
        result = {}
        for label, view, cells in [('sm', sm, raw_sm), ('pm', pm, raw_pm)]:
            reqs = [dict(seed=dict(zip(fields, c.inputs[0])), x=dict(zip(fields, c.inputs[1])),
                bw_writer=dict(world=c.node[0], runtime_rank=c.rank, microbatch=0, source_cid=c.node.cid,
                    call_instance=0, op='BW_sum', origin='nnscaler')) for c in cells if c.opname == 'BW_sum']
            result[label] = seed.map_requests(view, cells, reqs)
        return dict(inventories=result, pins={}, runs={})
    bind = feed.bind
    def attached(*args, **kwargs): return bind(*args, seed_bundle='fixture')
    with patch.object(feed, 'bind', attached), patch.object(seed, 'load_bundle', side_effect=inventory):
        return collective_world(root, k, normalize=True, project=True, seeded_transform=transform)


def layernorm_world(root, k, ndim=3, fault=None):
    return linear_world(root, k, ndim, fault, layernorm=True)


class ProductionSeedTests(unittest.TestCase):

    def test_softmax_positive_last_axis_computed_chain(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from scripts.tests.test_runtime_scoped_prefix import proof_text
        for k in (2, 3):
            for shape in ((2*k, 3), (k, 2, 3), (2, k, 1, 3)):
                with self.subTest(k=k, shape=shape), TemporaryDirectory() as d:
                    (Path(d)/'negative').mkdir()
                    (Path(d)/'positive').mkdir()
                    negative = linear_world(Path(d)/'negative', k, softmax=shape)
                    try:
                        positive = linear_world(Path(d)/'positive', k, softmax=shape, softmax_dim=len(shape)-1)
                    except ValueError as e:
                        self.fail(f'valid positive last axis rejected: {e}')
                    p = positive.receipt['scoped_prefix']['pm']
                    self.assertEqual(p['frontier']['op'], 'BW_div')
                    self.assertEqual(p['output_shape'], list(shape))
                    self.assertEqual(len(p['initial_premises']), 4*k)
                    text = proof_text(positive)
                    self.assertIn(':= fw_softmax ', text)
                    self.assertIn(':= bw_softmax ', text)
                    self.assertEqual(text, proof_text(negative))
                    self.assertEqual(positive.supporting_sources, negative.supporting_sources)
                    self.assertEqual(positive.lean, negative.lean)

    def test_softmax_ordinary_source_axis_contract(self):
        from types import SimpleNamespace as NS
        from Verdict.runtime_world import _ordinary
        for op in ('FW_softmax', 'BW_softmax'):
            inputs = ['x'] if op.startswith('FW_') else ['g', 'x']
            shapes = {'g': (2, 3), 'x': (2, 2, 3)}
            kw = {'dim': 2, 'dtype': None}
            view = NS(node_opname=lambda n: op, node_kwargs=lambda n: kw,
                node_inputs=lambda n: inputs, node_outputs=lambda n: ['out'],
                tensor_shape=lambda t: shapes[t])
            for dim in (-1, 2):
                kw['dim'] = dim
                self.assertEqual(_ordinary(view, None, lambda *a, **k: []), ([], None))
            for dim in (None, True, -1.0, 2.0, -4, 3, -2, 1):
                kw['dim'] = dim
                with self.subTest(op=op, dim=dim), self.assertRaisesRegex(ValueError, 'softmax axis'):
                    _ordinary(view, None, lambda *a, **k: [])
            kw['dim'] = -1
            shapes['x'] = ()
            with self.assertRaisesRegex(ValueError, 'softmax axis'):
                _ordinary(view, None, lambda *a, **k: [])
            shapes['x'] = (2, 2, 3)
            kw['dtype'] = 'float32'
            with self.assertRaisesRegex(ValueError, 'source parameter'):
                _ordinary(view, None, lambda *a, **k: [])
            kw['dtype'] = None
            while inputs:
                inputs.pop()
                self.assertEqual(_ordinary(view, None, lambda *a, **k: []), ([], 'unsupported-source-arity'))

    def test_bw_softmax_admission_controls(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from scripts.tests.test_runtime_scoped_prefix import proof_text
        for fault in ('g-uncomputed', 'x-uncomputed', 'g-shape', 'axis', 'axis-oob',
                      'axis-type', 'dtype', 'kwargs', 'consts', 'arity', 'outputs', 'output-shape'):
            with self.subTest(fault=fault), TemporaryDirectory() as d:
                if fault in ('axis', 'axis-oob', 'axis-type', 'dtype', 'kwargs', 'consts', 'outputs'):
                    with self.assertRaises(ValueError):
                        linear_world(Path(d), 2, softmax=(2, 2, 3), fault='softmax-'+fault)
                else:
                    fed = linear_world(Path(d), 2, softmax=(2, 2, 3), fault='softmax-'+fault)
                    self.assertEqual(fed.receipt['scoped_prefix']['pm']['frontier']['op'], 'BW_softmax')
                    self.assertNotIn(':= bw_softmax ', proof_text(fed))

    def test_bw_softmax_axis_and_kwargs_guards_independent(self):
        # Deliberately relax only the earlier ordinary-schema gate: the prefix
        # must still reject these source requests, not rely on that gate alone.
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from unittest.mock import patch
        from Verdict import runtime_world
        ordinary = runtime_world._ordinary
        def relaxed(view, node, get_params):
            if str(view.node_opname(node)).split('.')[-1] == 'BW_softmax':
                return [], None
            return ordinary(view, node, get_params)
        for fault in ('axis', 'axis-oob', 'axis-type', 'dtype', 'kwargs', 'consts'):
            with self.subTest(fault=fault), TemporaryDirectory() as d:
                with patch.object(runtime_world, '_ordinary', relaxed):
                    fed = linear_world(Path(d), 2, softmax=(2, 2, 3), fault='softmax-'+fault)
                frontier = fed.receipt['scoped_prefix']['pm']['frontier']
                self.assertEqual(frontier['op'], 'BW_softmax')
                self.assertEqual(frontier['reason'], 'bw-softmax-source-params')

    def test_bw_softmax_nonconstant_cpu_formula(self):
        import torch
        torch.set_num_threads(1)
        for shape in ((4, 3), (3, 2, 3), (2, 3, 2, 3)):
            x = (torch.arange(prod(shape), dtype=torch.float64).reshape(shape) % 7 / 3 - 1).requires_grad_()
            g = torch.arange(prod(shape), dtype=torch.float64).reshape(shape) % 5 - 2
            y = torch.softmax(x, dim=-1)
            actual, = torch.autograd.grad(y, x, g)
            recomputed = x.exp() / x.exp().sum(-1, keepdim=True)
            expected = recomputed * (g - (recomputed*g).sum(-1, keepdim=True))
            self.assertTrue(torch.isfinite(expected).all())
            self.assertTrue(torch.allclose(actual, expected, atol=1e-12, rtol=1e-12))
            self.assertFalse(torch.allclose(actual, g))
            wrong = x * (g - (x*g).sum(-1, keepdim=True))
            self.assertFalse(torch.allclose(actual, wrong))
            wrong_y = y.softmax(-1)
            self.assertFalse(torch.allclose(actual, wrong_y*(g-(wrong_y*g).sum(-1, keepdim=True))))

    def test_bw_softmax_computed_original_chain(self):
        import re
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from scripts.tests.test_runtime_scoped_prefix import proof_text
        for k in (2, 3):
            for shape in ((2*k, 3), (k, 2, 3), (2, k, 1, 3)):
                with self.subTest(k=k, shape=shape), TemporaryDirectory() as d:
                    fed = linear_world(Path(d), k, softmax=shape)
                    p = fed.receipt['scoped_prefix']['pm']; text = proof_text(fed)
                    self.assertEqual(p['frontier']['op'], 'BW_div')
                    self.assertEqual(len(p['initial_premises']), 4*k)
                    self.assertEqual(p['output_shape'], list(shape))
                    m = re.search(r'def pmSeededPrefixValue_(\d+)_0 .*:= bw_softmax (\(pmSeededPrefixValue_\d+_0 init\)) (\(pmSeededPrefixValue_\d+_0 init\))', text)
                    self.assertIsNotNone(m)
                    forward = re.search(r'def (pmSeededPrefixValue_\d+_0) .*:= fw_softmax '+re.escape(m[3]), text)
                    self.assertIsNotNone(forward)
                    self.assertNotEqual(m[3], '('+forward[1]+' init)')
                    for name in ('Read_'+m[1]+'_0', 'Read_'+m[1]+'_1', 'Step_'+m[1], 'Shape_'+m[1]+'_0'):
                        self.assertIn('theorem pmSeededPrefix'+name+' ', text)


    def test_bw_matmul_contract_controls(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from scripts.tests.test_runtime_scoped_prefix import proof_text
        faults = ('g-shape', 'contraction', 'batch', 'rank', 'g-uncomputed',
                  'a-uncomputed', 'b-uncomputed', 'input-arity', 'output-arity',
                  'duplicate', 'params', 'output-shape')
        for k in (2, 3):
            for fault in faults:
                with self.subTest(k=k, fault=fault), TemporaryDirectory() as d:
                    if fault in ('duplicate', 'params', 'output-arity'):
                        with self.assertRaises(ValueError):
                            linear_world(Path(d), k, matmul=3, fault='matmul-'+fault)
                    else:
                        fed = linear_world(Path(d), k, matmul=3, fault='matmul-'+fault)
                        self.assertEqual(fed.receipt['scoped_prefix']['pm']['frontier']['op'], 'BW_matmul')
                        self.assertNotIn(':= (batchedMatmulBwd ', proof_text(fed))

    def test_bw_matmul_nonsingleton_generated_chain(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from scripts.tests.test_runtime_scoped_prefix import proof_text
        for k in (2, 3):
            for rank, batch in ((2, ()), (3, (k,)), (4, (2, k))):
                with self.subTest(k=k, rank=rank), TemporaryDirectory() as d:
                    fed = linear_world(Path(d), k, matmul=rank, matmul_batch=batch)
                    p = fed.receipt['scoped_prefix']['pm']; text = proof_text(fed)
                    self.assertEqual(p['frontier']['op'], 'BW_multiref')
                    self.assertEqual(len(p['initial_premises']), 4*k)
                    import re
                    m = 2*k // prod(batch)
                    self.assertEqual(p['output_shape'], list(batch) + [3, m])
                    projections = re.findall(r'def pmSeededPrefixValue_(\d+)_(\d+) .*:= \(batchedMatmulBwd ((?:\(pmSeededPrefixValue_\d+_\d+ init\) ?){3})\)\.([12])', text)
                    self.assertEqual(len(projections), 2)
                    for step, port, operands, projection in projections:
                        self.assertEqual(int(projection), int(port)+1)
                        self.assertEqual(len(re.findall(r'pmSeededPrefixValue_', operands)), 3)
                        shape = list(batch) + ([m, 3] if port == '0' else [3, m])
                        self.assertRegex(text, rf'theorem pmSeededPrefixShape_{step}_{port} .* = {re.escape(str(shape))} :=')
                        self.assertRegex(text, rf'theorem pmSeededPrefixWritten_{step}_{port} .* = pmSeededPrefixValue_{step}_{port} init :=')

    def test_bw_matmul_legal_broadcast_only_rejected(self):
        import torch
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from scripts.tests.test_runtime_scoped_prefix import proof_text
        for k in (2, 3):
            with self.subTest(k=k), TemporaryDirectory() as d:
                a = torch.arange(6*k, dtype=torch.float32, requires_grad=True).reshape(k, 2, 3)
                b = torch.arange(15., requires_grad=True).reshape(1, 3, 5)
                g = torch.arange(10*k, dtype=torch.float32).reshape(k, 2, 5)
                da, db = torch.autograd.grad(a @ b, (a, b), g)
                self.assertEqual(tuple(da.shape), (k, 2, 3))
                self.assertEqual(tuple(db.shape), (1, 3, 5))
                fed = linear_world(Path(d), k, matmul=3, fault='matmul-broadcast-only')
                p = fed.receipt['scoped_prefix']['pm']; text = proof_text(fed)
                self.assertEqual(p['frontier']['op'], 'BW_matmul')
                self.assertEqual(p['frontier']['reason'], 'bw-matmul-shape-contract')
                self.assertEqual(p['frontier']['computed_shapes'], [[k, 2, 5], [k, 2, 3], [1, 3, 5]])
                self.assertNotIn(':= (batchedMatmulBwd ', text)

    def test_bw_matmul_both_computed_gradients(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from scripts.tests.test_runtime_scoped_prefix import proof_text
        for k in (2, 3):
            for rank in (2, 3, 4):
                with self.subTest(k=k, rank=rank), TemporaryDirectory() as d:
                    fed = linear_world(Path(d), k, matmul=rank)
                    p = fed.receipt['scoped_prefix']['pm']; text = proof_text(fed)
                    self.assertEqual(p['frontier']['op'], 'BW_multiref')
                    self.assertEqual(len(p['initial_premises']), 4*k)
                    for port in (1, 2):
                        self.assertRegex(text, rf'def pmSeededPrefixValue_\d+_{port-1} .*:= \(batchedMatmulBwd \(pmSeededPrefixValue_.*\)\)\.{port}')
    def test_internal_retained_single_root_accumulates_alias_branches(self):
        import torch
        from nnscaler.runtime.executor import Executor
        from nnscaler.runtime.function.function import multiref
        for n in (1, 2, 3):
            for level in (0, 1, 2):
                name = f'internal_multiref_test_{n}_{level}'
                x = torch.tensor([1., -2., 3.], requires_grad=True)
                g = torch.tensor([2., -1., 4.])
                def segment(t):
                    outputs = multiref(t, n, clone_level=level)
                    outputs = [outputs] if n == 1 else list(outputs)
                    return sum((y * g).sum() for y in outputs)
                loss = Executor.fexecute(name, segment, x)
                actual = Executor.backward(name, [x], [loss], [None])
                self.assertTrue(torch.equal(actual, n * g))
                self.assertEqual(Executor._detach.pop(name), [])

    def test_multiref_unbound_ordered_branches_fail_closed(self):
        import re
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from scripts.tests.test_runtime_scoped_prefix import proof_text
        for k in (2, 3):
            for n in (1, 2, 3):
                for repeated in (False, True):
                    with self.subTest(k=k, n=n, repeated=repeated), TemporaryDirectory() as d:
                        fed = linear_world(Path(d), k, layernorm=True, elementwise='equal', multiref=n, repeated=repeated)
                        p = fed.receipt['scoped_prefix']['pm']; text = proof_text(fed)
                        self.assertEqual(p['frontier']['op'], 'BW_multiref')
                        self.assertEqual(p['frontier']['reason'], 'missing-internal-autograd-edge-authority')
                        self.assertNotIn(':= tensorSum [', text)
    def test_multiref_source_and_computed_shape_controls(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from scripts.tests.test_runtime_scoped_prefix import proof_text
        for k in (2, 3):
            for fault in ('multiref-empty', 'multiref-params', 'multiref-consts', 'multiref-outputs', 'multiref-shape', 'multiref-output-shape', 'multiref-uncomputed', 'multiref-times'):
                with self.subTest(k=k, fault=fault), TemporaryDirectory() as d:
                    if fault in ('multiref-params', 'multiref-consts'):
                        with self.assertRaises(ValueError):
                            linear_world(Path(d), k, layernorm=True, elementwise='equal', multiref=2, fault=fault)
                    else:
                        fed = linear_world(Path(d), k, layernorm=True, elementwise='equal', multiref=0 if fault == 'multiref-empty' else 2, fault=fault)
                        self.assertEqual(fed.receipt['scoped_prefix']['pm']['frontier']['op'], 'BW_multiref')
                        self.assertNotIn(':= tensorSum [', proof_text(fed))
                        if fault == 'multiref-uncomputed':
                            self.assertEqual(fed.receipt['scoped_prefix']['pm']['frontier']['reason'], 'missing-internal-autograd-edge-authority')

    def test_multiref_nonconstant_cpu_branch_autograd(self):
        import torch
        for n in (1, 2, 3):
            for repeated in (False, True):
                x = torch.tensor([1., -2., 3.], dtype=torch.float64, requires_grad=True)
                grads = [torch.tensor([2.+q*3, -1.-q, 4.+q], dtype=torch.float64) for q in range(n)]
                grads.reverse()
                if repeated: grads[-1] = grads[0]
                from nnscaler.runtime.function.function import multiref
                branches = multiref(x, n)
                torch.autograd.backward([branches] if n == 1 else list(branches), grads)
                expected = sum(grads, torch.zeros_like(x))
                self.assertEqual(x.grad.tolist(), expected.tolist())
                self.assertGreater(expected.unique().numel(), 1)
                if n > 1:
                    self.assertFalse(torch.equal(x.grad, grads[0]))
                    self.assertFalse(torch.equal(x.grad, expected/n))

    def test_leaf_run_simplifies_steps_bottom_up_in_one_pass(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        import re
        from scripts.tests.test_runtime_scoped_prefix import proof_text
        with TemporaryDirectory() as d:
            text = proof_text(linear_world(Path(d), 3, layernorm=True, elementwise='broadcast'))
        leaves = re.findall(r'theorem \w+Run_\d+_\d+[^\n]* := by\n  simp only \[([^\n]+)\]', text)
        self.assertTrue(leaves)
        for rules in leaves:
            self.assertIn('Step_', rules)
        self.assertNotRegex(text, r'  rw \[pmSeededPrefixStep_')

    def test_add_broadcast_ordered_computed_outputs(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from scripts.tests.test_runtime_scoped_prefix import proof_text
        for k in (2, 3):
            for ndim in (2, 3):
                for mode in ('equal', 'broadcast'):
                    with self.subTest(k=k, ndim=ndim, mode=mode), TemporaryDirectory() as d:
                        fed = linear_world(Path(d), k, ndim, layernorm=True, elementwise=mode)
                        p = fed.receipt['scoped_prefix']['pm']; text = proof_text(fed)
                        self.assertEqual(p['frontier']['op'], 'BW_view')
                        self.assertEqual(len(p['initial_premises']), 4*k)
                        self.assertIn(':= (bw_add2 ', text)
                        for port in (0, 1):
                            import re
                            names = re.findall(r'def (pmSeededPrefixValue_\d+_'+str(port)+r') .* := \(bw_add2 ', text)
                            self.assertEqual(len(names), k)
                            for name in names:
                                self.assertRegex(text, r'def '+name+r' .* := \(bw_add2 .*\)\.'+str(port+1)+r'\n')
                                suffix = name.split('Value_')[1]
                                for role in ('Written', 'Shape'):
                                    self.assertIn('theorem pmSeededPrefix'+role+'_'+suffix, text)

    def test_gelu_exact_computed_and_controls(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from scripts.tests.test_runtime_scoped_prefix import proof_text
        for k in (2, 3):
            for fault in (None, 'gelu-dy', 'gelu-approx', 'gelu-params', 'gelu-arity', 'gelu-output'):
                with self.subTest(k=k, fault=fault), TemporaryDirectory() as d:
                    if fault in ('gelu-approx', 'gelu-params'):
                        with self.assertRaises(ValueError):
                            linear_world(Path(d), k, layernorm=True, elementwise='broadcast', fault=fault)
                        continue
                    fed = linear_world(Path(d), k, layernorm=True, elementwise='broadcast', fault=fault)
                    text = proof_text(fed); p = fed.receipt['scoped_prefix']['pm']
                    self.assertEqual(p['frontier']['op'], 'BW_gelu' if fault else 'BW_view')
                    self.assertEqual(':= bw_gelu ' in text, fault is None)
                    self.assertEqual(len(p['initial_premises']), 4*k)

    def test_gelu_nonconstant_cpu_exact_derivative(self):
        import torch, math
        x = torch.tensor([-3., -1., 0., .5, 2., 4.], dtype=torch.float64, requires_grad=True)
        dy = torch.tensor([2., -.5, 3., -2., 4., .7], dtype=torch.float64)
        torch.nn.functional.gelu(x, approximate='none').backward(dy)
        derivative = .5*(1+torch.erf(x.detach()/math.sqrt(2))) + x.detach()*torch.exp(-x.detach()**2/2)/math.sqrt(2*math.pi)
        torch.testing.assert_close(x.grad, dy*derivative, rtol=1e-12, atol=1e-12)
        self.assertFalse(torch.allclose(x.grad, dy))
        z = x.detach().requires_grad_()
        torch.nn.functional.gelu(z, approximate='tanh').backward(dy)
        self.assertFalse(torch.allclose(z.grad, x.grad, rtol=1e-8, atol=1e-8))

    def test_add_raw_source_and_shape_controls(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from scripts.tests.test_runtime_scoped_prefix import proof_text
        for k in (2, 3):
            for fault in ('add-alpha', 'add-params', 'add-arity', 'add-outputs', 'add-duplicate', 'add-dy', 'add-broadcast', 'add-dx', 'add-dyout'):
                with self.subTest(k=k, fault=fault), TemporaryDirectory() as d:
                    if fault in ('add-alpha', 'add-params', 'add-duplicate'):
                        with self.assertRaises(ValueError):
                            linear_world(Path(d), k, layernorm=True, elementwise='broadcast', fault=fault)
                    else:
                        fed = linear_world(Path(d), k, layernorm=True, elementwise='broadcast', fault=fault)
                        self.assertEqual(fed.receipt['scoped_prefix']['pm']['frontier']['op'], 'BW_add')
                        self.assertNotIn(':= (bw_add2 ', proof_text(fed))

    def test_add_nonconstant_cpu_both_broadcast_reductions(self):
        import torch
        for sx, sy in (((2, 1), (1, 3)), ((2, 3), (3,)), ((2, 3), (2, 3))):
            x = torch.arange(torch.tensor(sx).prod().item(), dtype=torch.float64).reshape(sx).requires_grad_()
            y = torch.arange(torch.tensor(sy).prod().item(), dtype=torch.float64).reshape(sy).requires_grad_()
            out = x + y
            dy = torch.arange(1, out.numel()+1, dtype=torch.float64).reshape(out.shape)
            out.backward(dy)
            for t in (x, y):
                expected = torch.zeros_like(t)
                import itertools
                for coord in itertools.product(*(range(d) for d in out.shape)):
                    target = tuple(0 if d == 1 else c for d, c in zip(t.shape, coord[len(out.shape)-len(t.shape):]))
                    expected[target] += dy[coord]
                torch.testing.assert_close(t.grad, expected)
                self.assertGreater(t.grad.unique().numel(), 1)

    def test_layernorm_three_ordered_outputs(self):
        import re
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from scripts.tests.test_runtime_scoped_prefix import proof_text
        for k in (2, 3):
            for ndim in (2, 3):
                with self.subTest(k=k, ndim=ndim), TemporaryDirectory() as d:
                    fed = layernorm_world(Path(d), k, ndim)
                    p = fed.receipt['scoped_prefix']['pm']; text = proof_text(fed)
                    self.assertEqual(p['frontier']['op'], 'BW_view')
                    self.assertEqual(len(p['initial_premises']), 4*k)
                    defs = re.findall(r'def (pmSeededPrefixValue_\d+_\d+) .* := \(bw_layernorm .*\)\.(1|2\.1|2\.2)\n', text)
                    self.assertEqual([v for _, v in defs], ['1', '2.1', '2.2'])
                    for name, _ in defs:
                        suffix = name.split('Value_')[1]
                        self.assertIn('theorem pmSeededPrefixWritten_' + suffix, text)
                        shape = [2*k, 3] if ndim == 2 else [1, 2*k, 3]
                        expected = shape if suffix.endswith('_0') else [3]
                        self.assertRegex(text, r'theorem pmSeededPrefixShape_' + suffix + r' .* = ' + re.escape(str(expected)) + r' :=')
                    for role in ('dx', 'dw', 'db'):
                        self.assertIn('bw_layernorm_' + role + '_shape', text)
                    self.assertIn('pmSeededPrefixFrame', text)
                    self.assertIn('pmSeededPrefixContinuation', text)

    def test_layernorm_source_and_shapes_fail_closed(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from scripts.tests.test_runtime_scoped_prefix import proof_text
        faults = ('epsilon', 'normalized-shape', 'ln-params', 'ln-arity', 'ln-outputs',
                  'duplicate-outputs', 'dy-shape', 'x-shape', 'gamma-shape', 'beta-shape',
                  'ln-dx', 'ln-dgamma', 'ln-dbeta')
        for k in (2, 3):
            for ndim in (2, 3):
                for fault in faults:
                    with self.subTest(k=k, ndim=ndim, fault=fault), TemporaryDirectory() as d:
                        if fault in ('epsilon', 'normalized-shape', 'ln-params', 'x-shape', 'gamma-shape', 'beta-shape', 'duplicate-outputs'):
                            with self.assertRaises(ValueError):
                                layernorm_world(Path(d), k, ndim, fault)
                            continue
                        fed = layernorm_world(Path(d), k, ndim, fault)
                        self.assertEqual(fed.receipt['scoped_prefix']['pm']['frontier']['op'], 'BW_layernorm')
                        self.assertNotIn(':= (bw_layernorm ', proof_text(fed))

    def test_layernorm_nonconstant_autograd_three_denote_formulas(self):
        import torch
        for shape in ((4, 3), (2, 2, 3)):
            x = torch.tensor([-.7, 2., 4., 1., -3., 2., 8., .5, -2., 3., 7., -1.], dtype=torch.float64).reshape(shape).requires_grad_()
            gamma = torch.tensor([.5, -2., 3.], dtype=torch.float64, requires_grad=True)
            beta = torch.tensor([7., -.2, 1.], dtype=torch.float64, requires_grad=True)
            dy = torch.tensor([2., -.4, 1., -3., 6., .5, 4., 2., -1., .7, 5., -2.], dtype=torch.float64).reshape(shape)
            torch.nn.functional.layer_norm(x, (3,), gamma, beta, 1e-5).backward(dy)
            xf, gf = x.detach().reshape(-1, 3), dy.reshape(-1, 3)
            mean = xf.sum(1, keepdim=True)/3
            var = ((xf-mean)**2).sum(1, keepdim=True)/3
            inv = 1/torch.sqrt(var+1e-5); hat = (xf-mean)*inv
            weighted = gf*gamma.detach()
            dx = inv/3*(3*weighted-weighted.sum(1, keepdim=True)-hat*(weighted*hat).sum(1, keepdim=True))
            dgamma = (gf*hat).sum(0); dbeta = gf.sum(0)
            for actual, expected in ((x.grad.reshape(-1, 3), dx), (gamma.grad, dgamma), (beta.grad, dbeta)):
                torch.testing.assert_close(actual, expected, rtol=1e-12, atol=1e-12)
                self.assertGreater(actual.unique().numel(), 1)
            self.assertFalse(torch.allclose(dgamma, dbeta))

    def test_bw_transpose_layout_family(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from scripts.tests.test_runtime_scoped_prefix import proof_text
        for k in (2, 3):
            for shape in ((3, 2*k), (3, k, 2), (1, 3, k, 2)):
                for a, b in ((0, -1), (-2, -1), (1, 1)):
                    with self.subTest(k=k, shape=shape, axes=(a,b)), TemporaryDirectory() as d:
                        fed = linear_world(Path(d), k, layout=('BW_transpose', {'dim0': a, 'dim1': b}, shape))
                        p = fed.receipt['scoped_prefix']['pm']; text = proof_text(fed)
                        self.assertEqual(p['frontier']['op'], 'BW_multiref')
                        self.assertEqual(len(p['initial_premises']), 4*k)
                        self.assertIn(f':= transposeAxes {a % len(shape)} {b % len(shape)} (pmSeededPrefixValue_', text)
            for fault in ('layout-arity', 'layout-initial', 'layout-dy', 'layout-output'):
                with self.subTest(k=k, fault=fault), TemporaryDirectory() as d:
                    fed = linear_world(Path(d), k, fault=fault, layout=('BW_transpose', {'dim0': 0, 'dim1': 1}, (3, 2*k)))
                    self.assertEqual(fed.receipt['scoped_prefix']['pm']['frontier']['op'], 'BW_transpose')
            for kw in ({}, {'dim0': True, 'dim1': 1}, {'dim0': -3, 'dim1': 1}, {'dim0': 0, 'dim1': 2}, {'dim0': 0, 'dim1': 1, 'unknown': 1}):
                with self.subTest(k=k, kw=kw), TemporaryDirectory() as d:
                    with self.assertRaises(ValueError): linear_world(Path(d), k, layout=('BW_transpose', kw, (3, 2*k)))

    def test_bw_transpose_requested_axes_not_output_authority(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from unittest.mock import patch
        from Verdict import graph_to_lean as c
        original = c._get_node_params
        def wrong(view, node, num_parts=0):
            params = original(view, node, num_parts=num_parts)
            return [0, 1] if str(view.node_opname(node)).endswith('BW_transpose') else params
        for k in (2, 3):
            with self.subTest(k=k), TemporaryDirectory() as d, patch.object(c, '_get_node_params', wrong):
                fed = linear_world(Path(d), k, layout=('BW_transpose', {'dim0': 1, 'dim1': 2}, (3, k, 2)))
                p = fed.receipt['scoped_prefix']['pm']
                self.assertEqual(p['frontier']['op'], 'BW_transpose')
                self.assertEqual(p['frontier']['reason'], 'bw-transpose-source-params')

    def test_bw_transpose_axis_sensitive_cpu_values(self):
        import torch
        from itertools import product
        for k in (2, 3):
            for shape in ((3, 2*k), (3, k, 2), (1, 3, k, 2), (k, k, k)):
                for a, b in ((0, -1), (-2, -1), (1, 1)):
                    x = torch.arange(__import__('math').prod(shape), dtype=torch.float64).reshape(shape).requires_grad_()
                    y = x.transpose(a, b)
                    g = torch.arange(1, x.numel()+1, dtype=torch.float64).reshape(y.shape)
                    y.backward(g)
                    expected = torch.empty_like(x)
                    for ix in product(*(range(d) for d in shape)):
                        src = list(ix); src[a], src[b] = src[b], src[a]
                        expected[ix] = g[tuple(src)]
                    self.assertTrue(torch.equal(x.grad, expected))
                    if a % len(shape) != b % len(shape) and shape[a] > 1 and shape[b] > 1:
                        self.assertFalse(torch.equal(x.grad.flatten(), g.flatten()))

    def test_bw_contiguous_layout_family(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from scripts.tests.test_runtime_scoped_prefix import proof_text
        for k in (2, 3):
            for shape in ((3, 2*k), (3, k, 2), (1, 3, k, 2)):
                with self.subTest(k=k, shape=shape), TemporaryDirectory() as d:
                    fed = linear_world(Path(d), k, layout=('BW_contiguous', {}, shape))
                    p = fed.receipt['scoped_prefix']['pm']; text = proof_text(fed)
                    self.assertEqual(p['frontier']['op'], 'BW_multiref')
                    self.assertEqual(len(p['initial_premises']), 4*k)
                    self.assertRegex(text, r'def pmSeededPrefixValue_\d+_0 .* := \(pmSeededPrefixValue_')
            for fault in ('layout-arity', 'layout-initial', 'layout-dy', 'layout-output'):
                with self.subTest(k=k, fault=fault), TemporaryDirectory() as d:
                    fed = linear_world(Path(d), k, fault=fault, layout=('BW_contiguous', {}, (3, 2*k)))
                    self.assertEqual(fed.receipt['scoped_prefix']['pm']['frontier']['op'], 'BW_contiguous')
            for kw in ({'memory_format': 'channels_last'}, {'unknown': 1}, {'__consts': [1]}):
                with self.subTest(k=k, kw=kw), TemporaryDirectory() as d:
                    with self.assertRaises(ValueError): linear_world(Path(d), k, layout=('BW_contiguous', kw, (3, 2*k)))

    def test_bw_contiguous_noncontiguous_cpu_values(self):
        import torch
        for k in (2, 3):
            for shape in ((3, 2*k), (3, k, 2), (1, 3, k, 2)):
                x = torch.arange(6*k, dtype=torch.float64).reshape(shape).transpose(-1, -2).detach().requires_grad_()
                self.assertFalse(x.is_contiguous())
                g = torch.arange(1, 6*k+1, dtype=torch.float64).reshape(x.shape)
                x.contiguous().backward(g)
                self.assertTrue(torch.equal(x.grad, g))

    def test_inverse_reshape_computed_source_request(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from scripts.tests.test_runtime_scoped_prefix import proof_text
        for k in (2, 3):
            for op, key in (('BW_view', 'size'), ('BW_reshape', 'shape')):
                for shape in ((3, 2*k), (3, k, 2), (1, 3, k, 2)):
                    with self.subTest(k=k, op=op, shape=shape), TemporaryDirectory() as d:
                        fed = linear_world(Path(d), k, inverse=(op, {key: (1, -1, 3)}, shape))
                        p = fed.receipt['scoped_prefix']['pm']; text = proof_text(fed)
                        if op == 'BW_reshape':
                            # No BW_reshape evalOp case: do not credit fallback identity.
                            self.assertEqual(p['frontier']['op'], 'BW_reshape')
                            continue
                        self.assertEqual(p['frontier']['op'], 'BW_layernorm')
                        self.assertEqual(len(p['initial_premises']), 4*k)
                        self.assertIn(f':= fw_view {list(shape)} (pmSeededPrefixValue_', text)
                        self.assertIn('pmSeededPrefixWritten_', text)
                        self.assertIn('pmSeededPrefixRead_', text)

    def test_inverse_view_rejects_initial_operands(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        for k in (2, 3):
            with self.subTest(k=k), TemporaryDirectory() as d:
                fed = linear_world(Path(d), k, fault='inverse-initial', inverse=('BW_view', {'size': (1, -1, 3)}, (3, 2*k)))
                self.assertEqual(fed.receipt['scoped_prefix']['pm']['frontier']['op'], 'BW_view')

    def test_inverse_view_source_shape_controls(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        for k in (2, 3):
            cases = [({}, None), ({'size': ()}, None), ({'size': (1, -1, -1)}, None),
                     ({'size': (True, 2*k, 3)}, None), ({'size': (1, 3, 2*k)}, None),
                     ({'size': (1, 2*k, 4)}, None), ({'size': (0, -1, 3)}, None)]
            cases += [({'size': (1, -1, 3)}, f) for f in ('inverse-arity', 'inverse-outputs', 'inverse-output', 'inverse-product')]
            for request, fault in cases:
                with self.subTest(k=k, request=request, fault=fault), TemporaryDirectory() as d:
                    if fault == 'inverse-outputs':
                        with self.assertRaisesRegex(ValueError, 'duplicate'):
                            linear_world(Path(d), k, fault=fault, inverse=('BW_view', request, (3, 2*k)))
                        continue
                    fed = linear_world(Path(d), k, fault=fault, inverse=('BW_view', request, (3, 2*k)))
                    self.assertEqual(fed.receipt['scoped_prefix']['pm']['frontier']['op'], 'BW_view')

    def test_inverse_view_nonconstant_cpu_autograd(self):
        import torch
        for k in (2, 3):
            for shape in ((3, 2*k), (3, k, 2), (1, 3, k, 2)):
                x = torch.arange(6*k, dtype=torch.float64).reshape(shape).requires_grad_()
                y = x.view(1, -1, 3)
                g = torch.arange(1, 6*k+1, dtype=torch.float64).reshape(y.shape)
                y.backward(g)
                self.assertEqual(tuple(x.grad.shape), shape)
                self.assertEqual(x.grad.flatten().tolist(), g.flatten().tolist())
                self.assertGreater(x.grad.unique().numel(), 1)

    def test_linear_two_outputs_computed_then_scattered(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from scripts.tests.test_runtime_scoped_prefix import proof_text
        for k in (2, 3):
            for ndim in (2, 3):
                with self.subTest(k=k, ndim=ndim), TemporaryDirectory() as d:
                    fed = linear_world(Path(d), k, ndim)
                    p = fed.receipt['scoped_prefix']['pm']; text = proof_text(fed)
                    self.assertEqual(p['frontier']['op'], 'BW_layernorm')
                    self.assertEqual(len(p['initial_premises']), 4*k)
                    self.assertIn(':= (bw_linear ', text)
                    self.assertIn(').1', text); self.assertIn(').2', text)
                    self.assertIn('bw_linear_' + ('3d_' if ndim == 3 else '') + 'fst_shape', text)
                    self.assertIn('bw_linear_' + ('3d_' if ndim == 3 else '') + 'snd_shape', text)
                    self.assertIn('reduceScatterPrimDimN', text)

    def test_linear_source_and_dimension_negative_controls(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from scripts.tests.test_runtime_scoped_prefix import proof_text
        for k in (2, 3):
            for ndim in (2, 3):
                for fault in ('bias', 'params', 'arity', 'outputs', 'dx-shape', 'dw-shape',
                              'grad-batch', 'grad-width', 'x-width', 'weight-dims'):
                    with self.subTest(k=k, ndim=ndim, fault=fault), TemporaryDirectory() as d:
                        if fault in ('bias', 'params'):
                            with self.assertRaisesRegex(ValueError, 'unsupported source parameter|unknown ordinary parameters'):
                                linear_world(Path(d), k, ndim, fault)
                            continue
                        fed = linear_world(Path(d), k, ndim, fault)
                        p = fed.receipt['scoped_prefix']['pm']
                        self.assertEqual(p['frontier']['op'], 'BW_linear')
                        self.assertNotIn(':= (bw_linear ', proof_text(fed))
                        if fault in ('grad-batch', 'grad-width', 'x-width', 'weight-dims'):
                            self.assertEqual(p['frontier']['reason'], 'bw-linear-shape-contract')
                        elif fault in ('dx-shape', 'dw-shape'):
                            self.assertEqual(p['frontier']['reason'], 'computed-source-shape-mismatch')

    def test_linear_nonconstant_cpu_autograd_matches_denote_indices(self):
        import torch
        for shape in ((2, 2), (2, 2, 2)):
            x = torch.arange(1, 1+torch.tensor(shape).prod().item(), dtype=torch.float64).reshape(shape).requires_grad_()
            w = torch.arange(1, 7, dtype=torch.float64).reshape(3, 2).requires_grad_()
            y = torch.nn.functional.linear(x, w, bias=None)
            dy = torch.arange(1, y.numel()+1, dtype=torch.float64).reshape(y.shape)
            y.backward(dy)
            xf, gf = x.detach().reshape(-1, 2).tolist(), dy.reshape(-1, 3).tolist()
            # Denote: dX contracts output features; dW sums flattened batch.
            dx = [[sum(g[j]*w[j, i].item() for j in range(3)) for i in range(2)] for g in gf]
            dw = [[sum(gf[b][j]*xf[b][i] for b in range(len(xf))) for i in range(2)] for j in range(3)]
            self.assertEqual(x.grad.reshape(-1, 2).tolist(), dx)
            self.assertEqual(w.grad.tolist(), dw)
            self.assertGreater(len(set(v for row in dx for v in row)), 1)
            self.assertGreater(len(set(v for row in dw for v in row)), 1)

    def test_explicit_production_attachment(self):
        self.assertIn('seed_bundle', inspect.signature(feed.bind).parameters)
        self.assertIsNone(inspect.signature(feed.bind).parameters['seed_bundle'].default)
        rows = seed.map_requests(*fixture(2)[:3])
        groups = seed.render_adapter({'sm': rows[:1], 'pm': rows}, structured=True)
        self.assertTrue(all(isinstance(g, prefix.ProofGroup) for g in groups))
        text, chunks = prefix.pack_proofs([groups])
        self.assertEqual(text.count('namespace TrainVerify.Denote.RuntimeWorld'), 1)
        self.assertIn('pmInitialWithSeeds_seed_1', text)
        self.assertIn('seed_inventories', inspect.signature(prefix.render).parameters)

    def test_cli_requires_handoff_before_loading(self):
        from unittest.mock import patch
        from Verdict import graph_to_lean as c
        with patch('sys.argv', ['graph_to_lean', '--out', 'never.lean', '--module', 'Never', '--runtime-seed-bundle', 'missing.json']):
            args = c.parse_args()
        with patch.object(c, 'load_verifier', side_effect=AssertionError('must not load')):
            with self.assertRaisesRegex(ValueError, 'seed bundle requires runtime input handoff'):
                c._generate(args)

    def test_seeded_cpu_source_k2_k3_and_failed_fresh_bind(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from types import SimpleNamespace as NS
        from unittest.mock import patch
        from Verdict import graph_to_lean as c
        from scripts.tests.test_runtime_scoped_prefix import collective_world, proof_text
        from scripts.tests.test_graph_to_lean_runtime_lineage import T, N, IR
        fields = ('world', 'runtime_rank', 'microbatch', 'source_tid', 'version')
        lower, bind = c._lower_runtime_graphs, feed.bind
        for k in (2, 3):
            for fault in (None, 'uncomputed-x'):
                captured = []
                def lowered(sm, pm):
                    for label, graph in [('s', sm), ('p', pm)]:
                        sources = [cell for cell in graph.cells if cell.opname == ('FW_embedding' if label == 's' else 'AllToAllPrim')]
                        for src in sources:
                            rank = src.rank; x = src.outputs[0]
                            g = T(label, rank, 0, 900, 0); y = T(label, rank, 0, 901, 1)
                            gir = IR(900, 'seed', (1,)); gir.is_grad = lambda: True
                            graph.shapes[g] = (1,); graph.shapes[y] = graph.shapes[x]
                            inp = g if fault == 'uncomputed-x' and label == 'p' else x
                            graph.cells.append(NS(node=N(label, rank, 0, 900, 'BW_sum'), rank=rank, opname='BW_sum', kwargs={},
                                inputs=[g, inp], outputs=[y], _input_irs=[gir, IR(inp.tid, 'x', graph.shapes[inp])],
                                _output_irs=[IR(901, 'gradient', graph.shapes[y])]))
                    return None
                def inventory(config, sm, pm, raw_sm, raw_pm, root):
                    if config == 'bad': raise ValueError('fresh authority rejected')
                    inventories = {}
                    for label, view, cells in [('sm', sm, raw_sm), ('pm', pm, raw_pm)]:
                        reqs = [dict(seed=dict(zip(fields, cell.inputs[0])), x=dict(zip(fields, cell.inputs[1])),
                            bw_writer=dict(world=cell.node[0], runtime_rank=cell.rank, microbatch=0, source_cid=cell.node.cid,
                                           call_instance=0, op='BW_sum', origin='nnscaler')) for cell in cells if cell.opname=='BW_sum']
                        inventories[label] = seed.map_requests(view, cells, reqs)
                    return dict(inventories=inventories, pins={}, runs={})
                def attached(*args, **kw):
                    captured.append(args)
                    return bind(*args, seed_bundle='fixture')
                # Only capture/event/PT authentication is mocked. Raw fullref mapping,
                # source world/feed checks, shape inference and atomic packing are real.
                with TemporaryDirectory() as d, patch.object(feed, 'bind', attached), patch.object(seed, 'load_bundle', side_effect=inventory):
                    fed = collective_world(Path(d), k, seeded_transform=lowered)
                    p = fed.receipt['scoped_prefix']['pm']; text = proof_text(fed)
                    if fault:
                        self.assertEqual(p['frontier']['reason'], 'unsupported-seed-sum-contract')
                    else:
                        self.assertIsNone(p['frontier'])
                        self.assertEqual(len(p['initial_premises']), k)
                        self.assertIn(':= bw_sum unitSeed', text)
                        self.assertIn('pmSeededPrefixState_0 (init : Store) : Store := (pmInitialWithSeeds init)', text)
                        self.assertIn('exact pmInitialWithSeeds_seed_', text)
                        self.assertIn('pmSeededDenoteWithInputs init = runUsing', text)
                        self.assertIn('pmInitialWithSeeds_frame init', text)
                        self.assertIn('= (pmInitialWithSeeds init) tid', text)
                        self.assertNotIn('def pmPrefixState_', text)
                    with self.assertRaisesRegex(ValueError, 'fresh authority rejected'):
                        bind(*captured[0], seed_bundle='bad')
                    plain = bind(*captured[0])
                    self.assertEqual(plain.receipt['scoped_prefix']['pm']['frontier']['reason'], 'unsupported-producer')
                    self.assertNotIn('seed_input', plain.receipt)
                    self.assertNotIn('pmInitialWithSeeds', proof_text(plain))
