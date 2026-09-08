"""Default CPU builder-unit tests with real nnScaler IR, not capture authentication.

The small execution-plan wrapper and lowered view below are explicit fixtures.
They do not authenticate original ModuleCodeGen/generated-code execution; the
external canonical capture audit covers that separate upstream boundary.
Installed nnScaler is required, not an optional/skipped dependency.
"""
import hashlib
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from types import SimpleNamespace as NS

import torch
from nnscaler.graph.segment import IRSegment
from nnscaler.ir.cten import IRCell
from nnscaler.ir.operator import IRFwOperation, IRBpOperation
from nnscaler.ir.tensor import IRFullTensor
from nnscaler_backend.build_graph import Cell
from nnscaler_backend.dfg import Node, Tensor
from verdict.graph import WType
from verdict.operators import OpName
from Verdict.runtime_multiref_authority import derive


class View:
    """Local lowered IDs; source refs retain world/rank/mb/tid/version."""
    def __init__(self, cells):
        self.cells = {c.node: c for c in cells}
        refs = dict.fromkeys(t for c in cells for t in c.inputs + c.outputs)
        self.ts = {t: NS(tid=i, ref=t) for i, t in enumerate(refs)}

    def tensors(self): return list(self.ts.values())
    def source_tensor(self, t): return t.ref
    def nodes(self): return list(self.cells)
    def node_opname(self, n): return self.cells[n].opname
    def node_kwargs(self, n): return self.cells[n].kwargs
    def node_inputs(self, n): return [self.ts[t] for t in self.cells[n].inputs]
    def node_outputs(self, n): return [self.ts[t] for t in self.cells[n].outputs]


class Fixture:
    """N real internal branches, independently replayed over K runtime ranks.

    Identity scale is intentional: no devices/collectives exist in this unit IR.
    Production derive still invokes the production execution-plan flatten helper.
    """
    def __init__(self, n=3, k=2):
        def tensor(name):
            t = IRFullTensor((2,), name=name, requires_grad=True,
                             dtype=torch.float32).tosub()
            t.grad = t.parent.grad.tosub()
            return t

        def op(name, inputs, outputs):
            fw = IRFwOperation(name, 'fixture.' + name, inputs, len(outputs))
            for p, t in enumerate(outputs): fw.set_output(p, t)
            bw = IRBpOperation([t.grad for t in outputs], [t.grad for t in inputs])
            IRCell.make_pair(fw, bw)
            return fw, bw

        self.x = tensor('input')
        self.outs = [tensor('branch') for _ in range(n)]
        self.fw, self.bw = op('multiref', [self.x], self.outs)
        ys = [tensor('consumer_result') for _ in range(n)]
        pairs = [op('consumer', [t], [y]) for t, y in zip(self.outs, ys)]
        self.consumers = [p[0] for p in pairs]
        self.mirrors = [p[1] for p in pairs]
        loss = tensor('loss')
        lossop, lossback = op('loss', ys, [loss])
        self.fnodes = [self.fw, *self.consumers, lossop]
        self.bnodes = [lossback, *reversed(self.mirrors), self.bw]
        self.segment = IRSegment(self.fnodes, [self.x], [loss])
        self.back = IRSegment(self.bnodes, [loss.grad], [])
        IRCell.make_pair(self.segment, self.back)
        self.seq = [self.segment, self.back]
        self.mg = NS(execplan=NS(seq=lambda rank: self.seq), scale=lambda ir, rank: ir)
        self.world = NS(plan_ndevs=1, runtime_ndevs=k)
        self.requests = [dict(seed=dict(runtime_rank=r), schedule_ordinal=1,
                              segment='segment' + str(self.segment.cid),
                              backward_cid=self.back.cid) for r in range(k)]
        self.cells = []
        for rank in range(k):
            for ir in self.fnodes + self.bnodes:
                c = Cell(ir, rank, WType('p'))
                c.node = Node(WType('p'), rank, 0, ir.cid, ir.name)
                c.opname = (OpName.FW_multiref if ir is self.fw else
                            OpName.BW_multiref if ir is self.bw else
                            OpName.FW_add if ir.isfw() else OpName.BW_add)
                ref = lambda t: Tensor(WType('p'), rank, 0, t.tid, 1)
                c.inputs = [ref(t) for t in ir.inputs()]
                c.outputs = [ref(t) for t in ir.outputs()]
                self.cells.append(c)
        self.view = View(self.cells)
        self.target = next(c for c in self.cells if c.ir is self.bw and c.rank == 0)

    def build(self, pins=None):
        return derive(self.view, self.cells, self.mg, self.world, self.requests,
                      {} if pins is None else pins)

    def reset_segments(self, fnodes=None, bnodes=None):
        # Preserve container identity while changing the independently retained IR.
        self.segment._nodes = self.fnodes if fnodes is None else fnodes
        self.back._nodes = self.bnodes if bnodes is None else bnodes


class SourceEdges(unittest.TestCase):
    def test_internal_nonempty_n_independent_of_runtime_k(self):
        for n in (1, 2, 3):
            for k in (2, 3):
                with self.subTest(n=n, k=k):
                    f = Fixture(n, k)
                    cert = f.build()
                    expected = {tuple(c.node) for c in f.cells if c.ir is f.bw}
                    self.assertEqual(cert.validate(f.view), expected)
                    rows = cert.receipt()['edges']
                    self.assertEqual(len(rows), k)
                    for row in rows:
                        c = next(c for c in f.cells if list(c.node) == row['backward_node'])
                        self.assertEqual([e['gradient_ref'] for e in row['edges']],
                                         [list(t) for t in c.inputs])
                        self.assertEqual([e['consumer_cid'] for e in row['edges']],
                                         [c.cid for c in f.consumers])
                        self.assertEqual([e['output_port'] for e in row['edges']], list(range(n)))

    def test_missing_wrong_segment_and_schedule_fail_closed(self):
        for fault in ('missing', 'wrong-segment', 'wrong-back', 'ordinal', 'order',
                      'duplicate-request', 'missing-request', 'segment-mirror', 'root'):
            with self.subTest(fault=fault):
                f = Fixture()
                if fault == 'missing': f.seq[:] = []
                elif fault == 'wrong-segment': f.requests[0]['segment'] = 'segment_missing'
                elif fault == 'wrong-back': f.requests[0]['backward_cid'] = -1
                elif fault == 'ordinal': f.requests[0]['schedule_ordinal'] = 0
                elif fault == 'order': f.seq.reverse()
                elif fault == 'duplicate-request': f.requests.append(dict(f.requests[0]))
                elif fault == 'missing-request': f.requests.pop(0)
                elif fault == 'segment-mirror': IRCell.make_pair(f.back, f.fw)
                else:
                    # Non-singleton root; invalidate nnScaler's cached accessor.
                    f.segment._outputs = [f.outs[0], f.outs[1]]
                    f.segment.outputs.cache_clear()
                with self.assertRaises(ValueError): f.build()

    def test_raw_cotangent_faults_fail_closed(self):
        for fault in ('reorder', 'delete', 'duplicate', 'unknown', 'result', 'writer',
                      'forward-raw-order', 'writer-owner'):
            with self.subTest(fault=fault):
                f = Fixture()
                if fault == 'reorder': f.target.inputs.reverse()
                elif fault == 'delete': f.target.inputs.pop()
                elif fault == 'duplicate': f.target.inputs[-1] = f.target.inputs[0]
                elif fault == 'unknown': f.target.inputs[0] = f.target.outputs[0]
                elif fault == 'result': f.target.outputs[0] = f.target.inputs[0]
                elif fault == 'forward-raw-order':
                    next(c for c in f.cells if c.rank == 0 and c.ir is f.fw).outputs.reverse()
                else:
                    writer = next(c for c in f.cells if c.rank == 0 and c.ir is f.mirrors[0])
                    if fault == 'writer-owner': writer.ir = f.mirrors[1]
                    else: writer.outputs[0] = f.target.outputs[0]
                self.assertNotIn(tuple(f.target.node), f.build().validate(f.view))

    def test_retained_ir_faults_fail_closed(self):
        for fault in ('outside-forward', 'outside-backward', 'consumer-missing',
                      'consumer-duplicate', 'consumer-order', 'backward-order',
                      'consumer-back-outside', 'consumer-mirror', 'multiref-mirror',
                      'duplicate-membership',
                      'boundary', 'partial-ir', 'input-gradient', 'returned-gradient'):
            with self.subTest(fault=fault):
                f = Fixture()
                if fault == 'outside-forward': f.reset_segments(f.fnodes[1:])
                elif fault == 'outside-backward': f.reset_segments(bnodes=f.bnodes[:-1])
                elif fault == 'duplicate-membership': f.reset_segments([f.fw, *f.fnodes])
                elif fault == 'consumer-missing': f.consumers[0].set_input(0, f.x)
                elif fault == 'consumer-duplicate': f.consumers[1].set_input(0, f.outs[0])
                elif fault == 'consumer-order': f.reset_segments([f.consumers[0], f.fw, *f.fnodes[2:]])
                elif fault == 'backward-order': f.reset_segments(bnodes=[f.bw, *f.bnodes[:-1]])
                elif fault == 'consumer-back-outside': f.reset_segments(bnodes=[n for n in f.bnodes if n is not f.mirrors[0]])
                elif fault == 'consumer-mirror': IRCell.make_pair(f.consumers[0], None)
                elif fault == 'multiref-mirror': IRCell.make_pair(f.fw, f.mirrors[0])
                elif fault == 'boundary': f.segment.set_output(0, f.outs[0])
                elif fault == 'partial-ir':
                    f.bw._inputs = list(f.bw.inputs())[:-1]
                    f.bw.inputs.cache_clear()
                elif fault == 'input-gradient': f.bw.set_output(0, f.outs[0].grad)
                else: f.mirrors[0].set_output(0, f.outs[1].grad)
                self.assertNotIn(tuple(f.target.node), f.build().validate(f.view))

    def test_coordinated_raw_and_ir_permutation_keeps_counts_but_rejects(self):
        f = Fixture()
        before = (len(f.target.inputs), len(f.bw.inputs()), len(f.cells))
        f.target.inputs.reverse()
        gs = list(f.bw.inputs())[::-1]
        for p, g in enumerate(gs): f.bw.set_input(p, g)
        self.assertEqual(before, (len(f.target.inputs), len(f.bw.inputs()), len(f.cells)))
        # Raw and BW IR now agree, but independent forward output.grad does not.
        # Permuting forward outputs too describes a different legal graph and is
        # deliberately NOT asserted invalid here.
        self.assertNotIn(tuple(f.target.node), f.build().validate(f.view))

    def test_rebound_view_full_reference_and_local_id(self):
        for fault in ('order', 'rank', 'local-id'):
            with self.subTest(fault=fault):
                f = Fixture()
                cert = f.build()
                if fault == 'order': f.target.inputs.reverse()
                else:
                    t = f.view.ts[f.target.inputs[0]]
                    if fault == 'rank': t.ref = t.ref._replace(rank=1)
                    else: t.tid += 10000
                with self.assertRaisesRegex(ValueError, 'stale/rebound'): cert.validate(f.view)

    def test_small_copied_source_pin_stale_missing_and_restored(self):
        import shutil
        with TemporaryDirectory() as d:
            original = Path(d) / 'original.py'
            copied = Path(d) / 'copied.py'
            original.write_text('def identity(x): return x\n')
            shutil.copyfile(original, copied)
            f = Fixture()
            cert = f.build({str(copied): hashlib.sha256(copied.read_bytes()).hexdigest()})
            self.assertIn(tuple(f.target.node), cert.validate(f.view))
            copied.write_text('def identity(x): return None\n')
            with self.assertRaisesRegex(ValueError, 'stale source'): cert.validate(f.view)
            copied.unlink()
            with self.assertRaises(FileNotFoundError): cert.validate(f.view)
            shutil.copyfile(original, copied)
            self.assertIn(tuple(f.target.node), cert.validate(f.view))


if __name__ == '__main__': unittest.main()
