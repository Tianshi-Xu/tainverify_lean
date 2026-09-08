"""Portable source -> raw DFG -> lossless compiler Chunk certificates."""
from collections import namedtuple
from copy import deepcopy
from types import SimpleNamespace
import unittest

from Verdict import graph_to_lean as compiler
from trainverify.runtime_source_authority import build_snapshot, bind_adapters

Tensor = namedtuple('Tensor', 'wtype rank mb tid v')
Node = namedtuple('Node', 'wtype rank mb cid irname')


def tref(t):
    return dict(zip(('world', 'runtime_rank', 'microbatch', 'source_tid', 'version'), t))


class Graph:
    def __init__(self, ranks=(2, 3), width=12):
        self.W = SimpleNamespace(runtime_ndevs=6, num_dp=2, num_mb=1)
        self.ns = [Node('p', 2, 0, 10, 'producer'), Node('p', 2, 0, 20, 'ChunkPrim')]
        self.ts = [Tensor('p', 2, 0, 77, 1), Tensor('p', 2, 0, 88, 1)]
        self.ins = {self.ns[0]: [], self.ns[1]: [self.ts[0]]}
        self.outs = {n: [t] for n, t in zip(self.ns, self.ts)}
        self.kw = dict(dim=1, ranks=list(ranks))
        self.shapes = {self.ts[0]: (4, width), self.ts[1]: (4, width // len(ranks))}
    def nodes(self): return self.ns
    def tensors(self): return self.ts
    def node_inputs(self, n): return self.ins[n]
    def node_outputs(self, n): return self.outs[n]
    def node_opname(self, n): return 'OpName.ChunkPrim' if n == self.ns[1] else 'OpName.FW_embedding'
    def node_kwargs(self, n): return self.kw if n == self.ns[1] else {}
    def tensor_shape(self, t): return self.shapes[t]


def fixture(ranks=(2, 3), width=12):
    g = Graph(ranks, width)
    writers = []
    for n in g.nodes():
        writers.append(dict(ref=dict(world=n.wtype, runtime_rank=n.rank, microbatch=n.mb,
            source_cid=n.cid, call_instance=0, op=g.node_opname(n).split('.')[-1], origin='nnscaler'),
            source_irname=n.irname, inputs=[tref(t) for t in g.node_inputs(n)],
            outputs=[tref(t) for t in g.node_outputs(n)]))
    s = build_snapshot(writers)
    s['runtime_ndevs'] = g.W.runtime_ndevs
    s['rank_sources'] = {str(r): f'class GenModel:\n    rank = {r}\n    world_size = 6\n    def __init__(self):\n        pass\n' for r in range(6)}
    s['rank_sources']['2'] += f'    def forward(self):\n        x_77 = torch.empty((4, {width}))\n        y_88 = nnscaler.runtime.adapter.chunk(x_77, dim=1, ranks={list(ranks)})\n'
    s['adapter_source'] = [{k: deepcopy(w[k]) for k in ('ref', 'inputs', 'outputs')} for w in s['writers']]
    s['adapter_source'][0]['generated_producer'] = dict(signature='torch.empty', inputs=[f'(4, {width})'], outputs=['x_77'], kwargs={})
    runtime = dict(module='nnscaler.runtime.adapter.collectives', name='chunk', source_file='portable/collectives.py',
        source='def chunk(itensor, dim, ranks, async_op=False):\n    group = DeviceGroup().get_group(ranks)\n    idx = torch.distributed.get_rank(group)\n    with torch.no_grad():\n        otensor = itensor.chunk(len(ranks), dim)[idx]\n        otensor = otensor.detach()\n    return otensor\n')
    s['adapter_source'][1]['primitive'] = dict(kind='ChunkPrim', signature='nnscaler.runtime.adapter.chunk',
        kwargs=deepcopy(g.kw), forward=True, generated_inputs=['x_77'], generated_outputs=['y_88'], runtime=runtime)
    s['writers'][1]['adapter_kwargs'] = deepcopy(g.kw)
    from trainverify.runtime_source_authority import bind_reducers
    for w in s['writers']:
        w['parameter_grad_tids'] = []
    bind_reducers(s)
    bind_adapters(s, allow_translation_mismatch=True)
    return g, s


class ChunkCompilerTests(unittest.TestCase):
    def test_source_to_same_graph_conditional_certificate(self):
        g, s = fixture()
        view, = compiler._lower_runtime_graphs(g)
        self.assertTrue(callable(getattr(compiler, 'attach_chunk_scopes', None)), 'missing connected Chunk compiler attachment')
        compiler.attach_chunk_scopes(view, s)
        self.assertIs(view.source, g)
        self.assertIs(view.nodes()[1], g.nodes()[1])
        self.assertEqual(len(view.tensors()), 2)
        req = view.chunk_scopes[g.ns[1]]
        self.assertEqual((req.ranks, req.local_index, req.dim), ((2, 3), 0, 1))
        self.assertFalse(req.proof_admissible)
        text = compiler.emit_chunk_scope_certificates(view)
        self.assertIn('GroupScopedEval.chunk_out', text)
        self.assertIn('hworld : g.numRanks = 6', text)
        self.assertIn('(s 0).shape = [4, 12]', text)
        self.assertIn('ins := [0], outs := [1]', text)
        self.assertEqual(text, compiler.emit_chunk_scope_certificates(view))


    def test_shapes_fail_closed_before_emission(self):
        for shape in ((4, 11), (4, 0), (0, 12), (4,), (4, -2)):
            g, s = fixture(); g.shapes[g.ts[0]] = shape
            view, = compiler._lower_runtime_graphs(g)
            with self.subTest(shape=shape), self.assertRaisesRegex(ValueError, 'Chunk.*shape'):
                compiler.attach_chunk_scopes(view, s)
        g, s = fixture(); g.shapes[g.ts[1]] = (4, 7)
        view, = compiler._lower_runtime_graphs(g)
        with self.assertRaisesRegex(ValueError, 'Chunk.*shape'):
            compiler.attach_chunk_scopes(view, s)

    def test_independent_raw_writer_not_coherently_repaired_snapshot(self):
        g, s = fixture()
        # Internally coherent source relabeling must not match the live raw producer.
        for w in s['writers']:
            if w['ref']['source_cid'] == 10:
                w['ref']['source_cid'] = 11
        s['adapter_source'][0]['ref']['source_cid'] = 11
        rebuilt = build_snapshot(s['writers'])
        s['writers'], s['tensors'] = rebuilt['writers'], rebuilt['tensors']
        bind_adapters(s, allow_translation_mismatch=True)
        view, = compiler._lower_runtime_graphs(g)
        with self.assertRaisesRegex(ValueError, 'source writer'):
            compiler.attach_chunk_scopes(view, s)

    def test_metadata_and_fullref_mutations(self):
        for mutation in ('world', 'rank', 'version', 'output', 'inputorder', 'dim', 'ranks', 'local_index', 'cardinality', 'source_writer', 'missing', 'unsupported'):
            g, s = fixture(); view, = compiler._lower_runtime_graphs(g)
            c = s['writers'][1]['chunk_scope']
            if mutation in ('world', 'rank', 'version'):
                field = dict(world='world', rank='runtime_rank', version='version')[mutation]
                c['inputs'][0][field] = 's' if mutation == 'world' else 9
            elif mutation == 'output': c['outputs'][0]['source_tid'] += 1
            elif mutation == 'inputorder': view._node2inputs[g.ns[1]] = list(view.tensors())[::-1]
            elif mutation == 'ranks': c['ranks'] = [3, 2]
            elif mutation in ('dim', 'local_index', 'cardinality'): c[mutation] += 1
            elif mutation == 'source_writer': c['source_writer'] = 'wrong'
            elif mutation == 'missing': del s['writers'][1]['chunk_scope']
            else:
                s['adapter_source'][1]['primitive']['runtime']['source'] = 'def chunk(itensor, dim, ranks, async_op=False):\n    return itensor\n'
                bind_adapters(s, allow_translation_mismatch=True)
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                compiler.attach_chunk_scopes(view, s)

    def test_held_out_noncontiguous_k3(self):
        g, s = fixture((0, 2, 5), width=15)
        view, = compiler._lower_runtime_graphs(g)
        compiler.attach_chunk_scopes(view, s)
        self.assertEqual(view.chunk_scopes[g.ns[1]].local_index, 1)
        self.assertIn('chunkPrimDimN 1 3 1', compiler.emit_chunk_scope_certificates(view))

    def test_rejected_generated_read_is_not_missing_conditional_authority(self):
        g, s = fixture()
        s['rank_sources']['2'] = s['rank_sources']['2'].replace('torch.empty', 'torch.ones')
        bind_adapters(s, allow_translation_mismatch=True)
        self.assertEqual(s['writers'][1]['chunk_scope']['generated_read_binding'], 'rejected')
        view, = compiler._lower_runtime_graphs(g)
        with self.assertRaisesRegex(ValueError, 'rejected.*read'):
            compiler.attach_chunk_scopes(view, s)

    def test_emitter_rejects_coherent_scope_and_lowered_node_tamper(self):
        from dataclasses import replace
        g, s = fixture(); view, = compiler._lower_runtime_graphs(g)
        compiler.attach_chunk_scopes(view, s)
        node = g.ns[1]
        view._node2inputs[node] = [view.node_outputs(node)[0]]
        view.chunk_scopes[node] = replace(view.chunk_scopes[node], input_tid=1)
        with self.assertRaisesRegex(ValueError, 'Chunk.*mismatch'):
            compiler.emit_chunk_scope_certificates(view)

    def test_real_ingress_attaches_before_lineage_blocker(self):
        from unittest.mock import patch
        from pathlib import Path
        g, s = fixture()
        v = SimpleNamespace(get_graph=lambda: (g, g), get_graph_compact=lambda: (g, g))
        args = SimpleNamespace(definitions_only=False, emit_spec_template=False, split_goals=False,
            emit_segment_patterns=False, out='unused-public.lean', spec_out='unused-spec.lean',
            sm_pkl='sm', pm_pkl='pm', verifier_cache_dir=None, runtime_rank_code_directory='source')
        observed = []
        def stop(sm, pm):
            observed.append(pm.chunk_scopes)
            raise ValueError('remaining DP lineage')
        with patch.object(compiler, 'load_verifier', return_value=v), \
             patch.object(compiler, '_load_chunk_source', return_value=s), \
             patch.object(compiler, 'aligned_logical_node_ids', return_value=({}, {})), \
             patch.object(compiler, 'infer_coarse_lineages_from_expanded', side_effect=stop):
            with self.assertRaisesRegex(ValueError, 'remaining DP lineage'):
                compiler._generate(args)
        self.assertEqual(len(observed[0]), 1)
        self.assertFalse(Path(args.out).exists())


if __name__ == '__main__':
    unittest.main()
