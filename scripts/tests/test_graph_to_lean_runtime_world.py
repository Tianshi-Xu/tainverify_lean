"""World definitions go through canonical runtime entry, never public goals."""
import unittest
from unittest.mock import patch
from types import SimpleNamespace as NS
from Verdict import graph_to_lean as c
from scripts.tests.test_graph_to_lean_runtime_lineage import fixture

class RuntimeWorldTests(unittest.TestCase):
    def test_entry_renders_complete_world_before_honest_public_block(self):
        sm, pm, authority = fixture()
        verifier = NS(get_graph=lambda: (sm, pm), get_graph_compact=lambda: (sm, pm))
        with patch('sys.argv', ['graph_to_lean', '--out', 'never-emitted.lean', '--module', 'Never']):
            args = c.parse_args()
        args.runtime_batch_authority = 'source.json'
        with patch.object(c, 'load_verifier', return_value=verifier), patch.object(c, '_load_runtime_lineage_inputs', return_value=authority):
            with self.assertRaises(ValueError) as caught:
                c._generate(args)
        result = caught.exception.receipt
        self.assertIn('world_definitions', result)
        world = result['world_definitions']
        self.assertEqual(world['sm_nodes'], 2)
        self.assertEqual(world['pm_nodes'], 8)
        self.assertFalse(world['execution_complete'])
        self.assertIn('input-adapter-unproved', {r['reason'] for r in world['missing']})
        self.assertIn('runtime-world-render/public-adapter', str(caught.exception))

class RendererTests(unittest.TestCase):
    def ordinary(self, units=2, tp=2):
        from Verdict.runtime_world import render
        sm, pm, a = fixture(units, tp)
        sv, pv = c._lower_runtime_graphs(sm, pm)
        return render, sv, pv, a

    def test_complete_nested_k2_k3_and_unknown_is_blocked(self):
        for k in (2, 3):
            render, sv, pv, a = self.ordinary(k, k)
            artifact = render(sv, pv, a[0], a[1])
            self.assertEqual(artifact.lean, render(sv, pv, a[0], a[1]).lean)
            self.assertEqual(artifact.lean.count(' : GraphDecl :='), 2)
            self.assertIn(f'numRanks := {k*k}', artifact.lean)
            self.assertEqual(artifact.lean.count('SourceScopedEval.denote'), 2)
            self.assertNotIn('InitGoal', artifact.lean)
        render, sv, pv, a = self.ordinary()
        cell = pv.source.cells[1]
        cell.opname = 'UNKNOWN_SOURCE_OP'; cell.kwargs = {}
        a[1][1].opname = cell.opname; a[1][1].kwargs = {}
        artifact = render(sv, pv, a[0], a[1])
        self.assertIn('unsupported-source-operation', str(artifact.receipt))
        self.assertIn('(pmNode_1, .group none, [])', artifact.lean)
        self.assertIn('pmNode_1_blocked', artifact.lean)

    def test_fresh_only_public_untouched(self):
        from Verdict.runtime_world import publish
        from pathlib import Path
        import tempfile
        render, sv, pv, a = self.ordinary()
        artifact = render(sv, pv, a[0], a[1])
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); public = root/'Public.lean'; public.write_bytes(b'untouched')
            out = root/'world'/'World.lean'; publish(artifact, out)
            self.assertEqual(out.read_text(), artifact.lean)
            with self.assertRaises(ValueError): publish(artifact, out)
            self.assertEqual(public.read_bytes(), b'untouched')

    def test_ordinary_inventory_sequence_params_and_shape_fail_closed(self):
        for fault in ('world', 'rank', 'order', 'raworder', 'port', 'version', 'params', 'shape', 'positive_shape', 'sourceop'):
            with self.subTest(fault=fault):
                render, sv, pv, a = self.ordinary(); n = pv.nodes()[1]
                if fault == 'world': pv.W.runtime_ndevs += 1
                elif fault == 'rank': pv._nodes[1] = n._replace(rank=999)
                elif fault == 'order': pv._nodes.reverse()
                elif fault == 'raworder': pv.source.cells.reverse(); pv._nodes.reverse()
                elif fault == 'port': pv._node2inputs[n].reverse()
                elif fault == 'version': pv._node2outputs[n][0] = pv._node2outputs[n][0]._replace(v=2)
                elif fault == 'params': pv.source.cell(n).kwargs['garbage'] = 1
                elif fault == 'shape': pv.source.shapes[pv.source.node_outputs(n)[0]] = (-1,)
                elif fault == 'positive_shape': pv.source.shapes[pv.source.node_outputs(n)[0]] = (999, 2, 6)
                else: a[1][1].opname = 'OTHER'
                with self.assertRaises(ValueError): render(sv, pv, a[0], a[1])

    def test_collectives_noncontiguous_and_stale_attachments(self):
        from scripts.tests.test_graph_to_lean_collective_scope import fixture as cf
        from dataclasses import replace
        from Verdict.runtime_world import render
        for op in ('AllToAllPrim', 'AllGatherPrim', 'ReduceScatterPrim', 'AllReducePrim'):
            for ranks in ((0,2), (0,2,5)):
                g, snapshot = cf(op, ranks)
                # Fixture producers have no source implementation: preserve but block.
                for n in g.ns[::2]: g.ops[n] = 'OpName.UNKNOWN_SOURCE_OP'
                for w in snapshot['writers'][::2]: w['ref']['op'] = 'UNKNOWN_SOURCE_OP'
                # Rebuild snapshot to authenticate changed producer identity.
                from trainverify.runtime_source_authority import build_snapshot, bind_adapters
                rebuilt = build_snapshot(snapshot['writers']); rebuilt['runtime_ndevs'] = g.W.runtime_ndevs
                rebuilt['adapter_source'] = snapshot['adapter_source']
                for row in rebuilt['adapter_source'][::2]: row['ref']['op'] = 'UNKNOWN_SOURCE_OP'
                bind_adapters(rebuilt)
                v, = c._lower_runtime_graphs(g); c.attach_collective_scopes(v, rebuilt)
                raw = [NS(node=n, opname=g.ops[n], kwargs=g.kw[n], inputs=g.ins[n], outputs=g.outs[n], _input_irs=[NS(shape=g.shapes[t]) for t in g.ins[n]], _output_irs=[NS(shape=g.shapes[t]) for t in g.outs[n]]) for n in g.ns]
                sm, _, a = fixture(); sv, = c._lower_runtime_graphs(sm)
                # Use one joint namespace, never reuse independently lowered IDs.
                sv, v = c._lower_runtime_graphs(sm, g); c.attach_collective_scopes(v, rebuilt)
                artifact = render(sv, v, a[0], raw)
                self.assertIn(f'.group (some {list(ranks)})', artifact.lean)
                self.assertEqual(artifact.receipt['pm_nodes'], 2*len(ranks))
                n = g.ns[1]; original = v.collective_scopes[n]
                for bad in (replace(original, ranks=tuple(reversed(ranks))), replace(original, input_tids=tuple(reversed(original.input_tids))), replace(original, output_tid=999), replace(original, params=(999,))):
                    v.collective_scopes[n] = bad
                    with self.assertRaises(ValueError): render(sv, v, a[0], raw)
                v.collective_scopes[n] = original
                from copy import copy
                for removed in (('_collective_source',), ('_collective_source', '_chunk_source')):
                    with self.subTest(op=op, ranks=ranks, removed=removed):
                        render(sv, v, a[0], raw)
                        bad_view = copy(v)
                        bad_view.collective_scopes = dict(v.collective_scopes)
                        for field in removed: delattr(bad_view, field)
                        bad_view.collective_scopes[n] = replace(original, params=(999,))
                        with self.assertRaises(ValueError): render(sv, bad_view, a[0], raw)

class StrictRawTests(unittest.TestCase):
    def layernorm_world(self, norm=(3,), backward=False):
        from copy import deepcopy
        from scripts.tests.test_graph_to_lean_runtime_lineage import Graph, IR, T
        sm, _, a = fixture(); pm = Graph('p', 1, 1)
        x,w,b,y=(IR(610,'x',(2,3)),IR(611,'w',tuple(norm),param=True),
                 IR(612,'b',tuple(norm),param=True),IR(613,'y',(2,3)))
        ins,outs=[x,w,b],[y]
        if backward:
            ins=[IR(614,'grad',(2,3)),*ins]
            outs=[y,IR(615,'dw',tuple(norm)),IR(616,'db',tuple(norm))]
        tensors=ins+outs
        refs={i.tid:T('p',0,-1 if i.param else 0,i.tid,0 if i.param else 1) for i in tensors}
        cell=pm.cells[1];cell.opname='BW_layernorm' if backward else 'FW_layernorm'
        cell.kwargs=dict(normalized_shape=list(norm),eps=1e-5)
        cell.inputs=[refs[i.tid] for i in ins];cell.outputs=[refs[i.tid] for i in outs]
        cell._input_irs=ins;cell._output_irs=outs
        pm.cells=[cell];pm.shapes={refs[i.tid]:i.shape for i in tensors}
        raw=deepcopy(pm.cells);sv,pv=c._lower_runtime_graphs(sm,pm)
        return sv,pv,a[0],raw

    def test_layernorm_fixed_epsilon_and_last_axis_domain(self):
        from Verdict.runtime_world import render
        for backward in (False,True):
            with self.subTest(backward=backward):
                sv,pv,rs,rp=self.layernorm_world(backward=backward)
                self.assertIn('(pmNode_0, .global, [])',render(sv,pv,rs,rp).lean)
                pv.source.cells[0].kwargs['eps']=0.5;rp[0].kwargs['eps']=0.5
                with self.assertRaisesRegex(ValueError,'epsilon'):render(sv,pv,rs,rp)

    def test_layernorm_multi_axis_source_is_not_last_axis_denote(self):
        from Verdict.runtime_world import render
        for backward in (False,True):
            with self.subTest(backward=backward):
                self.assertIn('(pmNode_0, .global, [])',render(*self.layernorm_world(backward=backward)).lean)
                with self.assertRaisesRegex(ValueError,'normalized shape'):
                    render(*self.layernorm_world((2,3),backward))

    def test_tensor_inventory_iteration_does_not_change_artifact_bytes(self):
        from Verdict.runtime_world import render
        sm, pm, a = fixture(); sv, pv = c._lower_runtime_graphs(sm, pm)
        first = render(sv, pv, a[0], a[1])
        sm.shapes = dict(reversed(list(sm.shapes.items())))
        pm.shapes = dict(reversed(list(pm.shapes.items())))
        sv, pv = c._lower_runtime_graphs(sm, pm)
        second = render(sv, pv, a[0], a[1])
        self.assertEqual(first.lean, second.lean)
        self.assertEqual(first.receipt, second.receipt)

    def test_missing_raw_ports_rejected(self):
        from Verdict.runtime_world import render
        sm, pm, a = fixture(); sv, pv = c._lower_runtime_graphs(sm, pm)
        a[1][1].inputs = None
        with self.assertRaises(ValueError): render(sv, pv, a[0], a[1])

    def test_duplicate_nodedecl_cannot_acquire_different_meaning(self):
        from Verdict.runtime_world import render
        sm, pm, a = fixture(); sv, pv = c._lower_runtime_graphs(sm, pm)
        pv._nodes.append(pv._nodes[1])
        with self.assertRaisesRegex(ValueError, 'sequence'): render(sv, pv, a[0], a[1])

if __name__ == '__main__': unittest.main()
