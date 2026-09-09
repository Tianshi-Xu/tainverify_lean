"""Source order is identity, not a legal global execution order."""
import copy
import re
import unittest
from Verdict import graph_to_lean as c
from Verdict.runtime_world import render
from scripts.tests.test_graph_to_lean_runtime_lineage import Graph, IR, T


def cross_rank(k):
    sm, pm = Graph('s', 1, 1), Graph('p', 1, k)
    cells = []
    for rank in range(k):
        loader, producer = pm.cells[2*rank:2*rank+2]
        reader = copy.deepcopy(producer)
        reader.node = reader.node._replace(cid=19, irname='FW_add')
        reader.opname = 'FW_add'; reader.kwargs = {}
        # Deliberately retain peer order, not sorted rank or tensor order.
        reader.inputs = [pm.cells[2*((rank+1)%k)+1].outputs[0], producer.outputs[0]]
        out = T('p', rank, 0, 40, 1)
        pm.shapes[out] = pm.shapes[producer.outputs[0]]
        reader.outputs = [out]
        reader._input_irs = [IR(t.tid, 'y', pm.shapes[t]) for t in reader.inputs]
        reader._output_irs = [IR(40, 'z', pm.shapes[out])]
        cells.extend([loader, producer, reader])
    pm.cells = cells
    sv, pv = c._lower_runtime_graphs(sm, pm)
    return sv, pv, copy.deepcopy(sm.cells), copy.deepcopy(pm.cells)


def graph_order(lean, label):
    line = next(x for x in lean.splitlines() if x.startswith(f'def {label}Graph :'))
    return [int(x) for x in re.findall(label+r'Node_(\d+)', line)]


def forward_reads(view, order):
    pos = {i:j for j,i in enumerate(order)}
    writers = {view.source_tensor(t):i for i,n in enumerate(view.nodes()) for t in view.node_outputs(n)}
    return [(i,port,writers[view.source_tensor(t)]) for i,n in enumerate(view.nodes())
            for port,t in enumerate(view.node_inputs(n))
            if view.source_tensor(t) in writers and pos[writers[view.source_tensor(t)]] >= pos[i]]


class ScheduleTests(unittest.TestCase):
    def test_cross_rank_source_failure_then_legal_world(self):
        for k in (2, 3):
            with self.subTest(k=k):
                sv,pv,rs,rp = cross_rank(k)
                original = tuple(pv.nodes())
                old = list(range(len(original)))
                self.assertTrue(forward_reads(pv, old))
                artifact = render(sv,pv,rs,rp)
                order = graph_order(artifact.lean, 'pm')
                self.assertEqual(forward_reads(pv, order), [])
                self.assertEqual(sorted(order), old)
                self.assertEqual(tuple(pv.nodes()), original)
                for rank in range(k):
                    self.assertEqual([i for i in order if original[i].rank==rank],
                                     [i for i in old if original[i].rank==rank])
                # A small value witness: source-major reads sentinel 999,
                # legal interleaving reads the actual producer's rank+1.
                def evaluate(indices):
                    store={}; values=[]
                    for i in indices:
                        n=original[i]
                        if i%3==1: store[pv.node_outputs(n)[0].tid]=n.rank+1
                        if i%3==2: values.append(sum(store.get(t.tid,999) for t in pv.node_inputs(n)))
                    return values
                self.assertTrue(any(x>=999 for x in evaluate(old)))
                self.assertTrue(all(x<999 for x in evaluate(order)))
                for i,n in enumerate(original):
                    self.assertIn(f'ins := {[t.tid for t in pv.node_inputs(n)]}', artifact.lean.split(f'def pmNode_{i} :')[1].split('\n')[0])

    def test_invalid_permutations_and_fullref_dependencies(self):
        from Verdict.runtime_schedule import build, validate
        sv,pv,rs,rp = cross_rank(3)
        schedule = build(pv)
        order = schedule['execution_to_source']
        self.assertEqual(build(pv), schedule)
        for candidate in (order[:-1], order+[order[0]], [True]+order[1:],
                          [999]+order[1:], list(range(len(order))), list(reversed(order))):
            with self.subTest(candidate=candidate), self.assertRaises(ValueError):
                validate(pv, candidate)
        self.assertEqual([order[j] for j in schedule['source_to_execution']], list(range(len(order))))
        self.assertTrue(schedule['external_leaves'])
        self.assertFalse(schedule['external_initial_values_proved'])
        self.assertTrue(all(not leaf['initial_value_proved'] for leaf in schedule['external_leaves']))

    def test_cycle_self_read_and_missing_inventory_fail_closed(self):
        for fault in ('cycle', 'self-read', 'missing', 'world', 'rank', 'port', 'version', 'duplicate'):
            with self.subTest(fault=fault):
                sv,pv,rs,rp = cross_rank(2)
                if fault in ('cycle', 'self-read', 'duplicate'):
                    # New independently lowered source graph, not a forged schedule.
                    g = pv.source
                    if fault == 'cycle':
                        g.cells[1].inputs[0] = g.cells[2].outputs[0]
                        g.cells[1]._input_irs[0] = copy.deepcopy(g.cells[2]._output_irs[0])
                    elif fault == 'self-read':
                        g.cells[2].inputs[0] = g.cells[2].outputs[0]
                    else: g.cells[2].outputs[0] = g.cells[1].outputs[0]
                    if fault == 'duplicate':
                        with self.assertRaisesRegex(ValueError, 'duplicate'): c._lower_runtime_graphs(sv.source,g)
                        continue
                    sv,pv = c._lower_runtime_graphs(sv.source,g)
                    rp = copy.deepcopy(g.cells)
                elif fault == 'missing': pv._tensors.pop()
                elif fault == 'world': pv.W.runtime_ndevs += 1
                elif fault == 'rank': pv._nodes[0] = pv._nodes[0]._replace(rank=100)
                elif fault == 'port': pv._node2inputs[pv.nodes()[2]].reverse()
                else:
                    n=pv.nodes()[2]; pv._node2inputs[n][0]=pv._node2inputs[n][0]._replace(v=99)
                with self.assertRaises(ValueError): render(sv,pv,rs,rp)

    def test_feed_consumes_canonical_permutation_and_rejects_forgery(self):
        import tempfile
        from pathlib import Path
        from dataclasses import replace
        from Verdict.runtime_input_feed import bind
        from scripts.tests.test_runtime_input_feed import observed
        for k in (2, 3):
            with self.subTest(k=k), tempfile.TemporaryDirectory() as d:
                root=Path(d); authority=observed(root,1,k)
                sv,pv,rs,rp=cross_rank(k)
                world=render(sv,pv,rs,rp)
                fed=bind(world,sv,pv,rs,rp,*authority,root)
                data = fed.supporting_sources['TrainVerifyRuntimeWorldData.lean']
                for label in ('sm','pm'):
                    requests=data.split(f'def {label}InputRequests : List InputRequest := [')[1].split(']')[0]
                    self.assertEqual([int(x) for x in re.findall(label+r'Node_(\d+),',requests)],graph_order(data,label))
                for fault in ('omit','reverse','inverse','metadata','lean'):
                    receipt=copy.deepcopy(world.receipt); lean=world.lean
                    s=receipt['execution_order']['pm']
                    if fault=='omit': s['execution_to_source'].pop()
                    elif fault=='reverse': s['execution_to_source'].reverse()
                    elif fault=='inverse': s['source_to_execution'].reverse()
                    elif fault=='metadata': s['dependency_order_validated']=False
                    else: lean=lean.replace('nodes := [pmNode_0,', 'nodes := [pmNode_1,',1)
                    with self.subTest(fault=fault), self.assertRaisesRegex(ValueError,'current source authority'):
                        bind(replace(world,lean=lean,receipt=receipt),sv,pv,rs,rp,*authority,root)


if __name__ == '__main__': unittest.main()
