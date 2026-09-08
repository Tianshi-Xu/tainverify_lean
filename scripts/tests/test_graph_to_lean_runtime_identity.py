"""Portable compiler-local full-reference identity tests (no capture/cache dependency)."""
from collections import namedtuple
from types import SimpleNamespace
import unittest

from Verdict import graph_to_lean as compiler

Tensor = namedtuple("Tensor", "wtype rank mb tid v")
Node = namedtuple("Node", "wtype rank mb cid irname")


class Graph:
    def __init__(self, world="p", dp=2):
        self.W = SimpleNamespace(num_dp=dp, num_mb=1, num_tp=2)
        a = Tensor(world, -1, -1, 7, 0)
        b = Tensor(world, 0, 0, 7, 1)
        c = Tensor(world, 2, 0, 7, 1)
        d = Tensor(world, 0, 0, 7, 2)
        self.refs = [a, b, c, d]
        self.ns = [Node(world, r, 0, i, "float") for i, r in enumerate([0, 2, 0])]
        self.ins = dict(zip(self.ns, [[a], [a], [b, c]]))
        self.outs = dict(zip(self.ns, [[b], [c], [d]]))
        self.ops = dict(zip(self.ns, ["OpName.FW_float"] * 3))

    def nodes(self): return self.ns
    def tensors(self): return self.refs
    def node_inputs(self, n): return self.ins[n]
    def node_outputs(self, n): return self.outs[n]
    def node_opname(self, n): return self.ops[n]
    def node_kwargs(self, n): return {}
    def node_dtag(self, n): return n.rank
    def tensor_shape(self, t): return (t.rank + 3, t.v + 1)
    def is_initialized(self, t): return t.v == 0


class RuntimeIdentityTests(unittest.TestCase):
    def test_export_lowers_before_precise_lineage_blocker(self):
        from unittest.mock import patch
        from pathlib import Path
        import tempfile
        sm, pm = Graph("s", 1), Graph()
        verifier = SimpleNamespace(get_graph=lambda: (sm, pm), get_graph_compact=lambda: (sm, pm))
        with tempfile.TemporaryDirectory(dir=Path(__file__).resolve().parents[2]) as root:
            out = Path(root) / "fresh" / "GeneratedData.lean"
            argv = ["graph_to_lean", "--out", str(out), "--module", "FreshDP.GeneratedData", "--definitions-only"]
            with patch("sys.argv", argv), patch.object(compiler, "load_verifier", return_value=verifier):
                with self.assertRaisesRegex(ValueError, "runtime-identity lineage reconstruction is unavailable"):
                    compiler._generate(compiler.parse_args())
            self.assertFalse(out.parent.exists())

    def test_direct_emitter_cannot_publish_a_lowered_view(self):
        from pathlib import Path
        import tempfile
        view, = compiler._lower_runtime_graphs(Graph())
        with tempfile.TemporaryDirectory(dir=Path(__file__).resolve().parents[2]) as root:
            out = Path(root) / "fresh" / "GeneratedData.lean"
            with self.assertRaisesRegex(ValueError, "runtime-identity.*scope"):
                compiler.emit_lean_spec(
                    out_path=out, spec_out_path=None, emit_spec_template=False,
                    overwrite_spec=False, module_name="FreshDP.GeneratedData",
                    sm_nodes=[], pm_nodes=[], sm_graph=view, pm_graph=view,
                    sm_logical_ids={}, pm_logical_ids={}, sm_input_value_classes=[],
                    pm_input_value_classes=[], init_goals=[], goals=[], definitions_only=True)
            self.assertFalse(out.parent.exists())

    def test_empty_special_contract_checks_both_complete_graphs(self):
        sm, pm = Graph("s", 1), Graph()
        self.assertEqual(compiler.aligned_logical_node_ids(sm, pm), ({}, {}))
        for side in (sm, pm):
            for op in compiler.REPLICA_GROUP_OPS:
                side.ops[side.ns[-1]] = op
                with self.assertRaisesRegex(ValueError, "exact subgroup scope"):
                    compiler.aligned_logical_node_ids(sm, pm)
                side.ops[side.ns[-1]] = "OpName.FW_float"

    def test_malformed_graphs_fail_before_export(self):
        for fault, message in (("unknown", "unknown full tensor reference"),
                               ("duplicate", "duplicate full tensor writer")):
            graph = Graph()
            if fault == "unknown":
                graph.ins[graph.ns[-1]].append(Tensor("p", 3, 0, 999, 1))
            else:
                graph.outs[graph.ns[-1]].append(graph.refs[1])
            with self.assertRaisesRegex(ValueError, message):
                compiler._lower_runtime_graphs(graph)

    def test_generic_dp1_lowered_view_is_not_the_legacy_quotient(self):
        graph = Graph(dp=1)
        view, = compiler._lower_runtime_graphs(graph)
        self.assertEqual(len({t.tid for t in view.tensors()}), len(graph.tensors()))
        for node in graph.nodes():
            self.assertEqual([view.source_tensor(t) for t in view.node_outputs(node)], graph.node_outputs(node))
        shapes = compiler._all_tensor_shapes_from_graph(view)
        self.assertEqual(shapes, {t.tid: list(graph.tensor_shape(view.source_tensor(t))) for t in view.tensors()})
        lines = []
        compiler._emit_init_env(lines, name="pm", G=view, kept_nodes=view.nodes(), emit_all_shapes=True)
        for t in view.tensors():
            self.assertIn(f"({t.tid}, {list(view.tensor_shape(t))})", "\n".join(lines))

    def test_ordered_adapter_records_keep_peer_outputs_and_versions(self):
        graph = Graph()
        # Two rank-local reducer/adapter outputs share raw tid and input list.
        old0 = Tensor("p", 0, -1, 7, 1)
        old2 = Tensor("p", 2, -1, 7, 1)
        new0, new2 = old0._replace(v=2), old2._replace(v=2)
        graph.refs = [old0, old2, new0, new2]
        graph.ns = graph.ns[:2]
        graph.ins = {n: [old0, old2] for n in graph.ns}
        graph.outs = dict(zip(graph.ns, [[new0], [new2]]))
        graph.ops = {n: "OpName.AllReducePrim" for n in graph.ns}
        graph.node_kwargs = lambda n: {"ranks": [0, 2]}
        view, = compiler._lower_runtime_graphs(graph)
        rows = compiler.derive_adapter_communications(view, view.nodes())
        self.assertEqual(len(rows), 2)
        by_id = {t.tid: view.source_tensor(t) for t in view.tensors()}
        self.assertEqual([by_id[row.primary_out_tid] for row in rows], [new0, new2])
        for row in rows:
            self.assertEqual([by_id[tid] for rank, tid in row.inputs], [old0, old2])
        self.assertEqual(compiler._stable_toposort_nodes(view, view.nodes()), graph.nodes())
        self.assertEqual(len(compiler.final_writer_ranks_by_tid(view, view.nodes())), 2)

    def test_lossless_rank_world_version_roundtrip(self):
        source = Graph()
        sm = Graph("s", dp=1)
        sm_compact = Graph("s", dp=1)
        self.assertTrue(callable(getattr(compiler, "_lower_runtime_graphs", None)),
                        "compiler needs a connected lossless full-reference graph view")
        gs, gc, gp = compiler._lower_runtime_graphs(sm, sm_compact, source)
        self.assertEqual(len({t.tid for t in gp.tensors()}), 4)
        self.assertEqual([t.tid for t in gs.tensors()], [t.tid for t in gc.tensors()])
        self.assertTrue({t.tid for t in gs.tensors()}.isdisjoint(t.tid for t in gp.tensors()))
        for raw, lowered in zip(source.tensors(), gp.tensors()):
            self.assertEqual(gp.source_tensor(lowered), raw)
            self.assertEqual(gp.tensor_shape(lowered), source.tensor_shape(raw))
            self.assertEqual(gp.is_initialized(lowered), source.is_initialized(raw))
        for n in source.nodes():
            self.assertIs(next(x for x in gp.nodes() if x == n), n)
            for method in ("node_inputs", "node_outputs"):
                self.assertEqual([gp.source_tensor(t) for t in getattr(gp, method)(n)],
                                 getattr(source, method)(n))
        self.assertEqual(compiler._stable_toposort_nodes(gp, gp.nodes()), source.nodes())
        self.assertEqual(source.refs[0].tid, 7)  # backend untouched
        self.assertEqual(len(compiler.backward_closure_tids(gp, [gp.node_outputs(gp.nodes()[-1])[0].tid])), 4)
        self.assertEqual(compiler._init_tids_from_kept_nodes(gp, gp.nodes()), [gp.tensors()[0].tid])


if __name__ == "__main__":
    unittest.main()
