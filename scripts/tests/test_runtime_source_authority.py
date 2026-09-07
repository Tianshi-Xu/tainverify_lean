"""Focused source-only tests; constructed cases are not real captures."""
import importlib
import importlib.util
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT), str(ROOT / "Verdict")]


class IdentityTests(unittest.TestCase):
    def test_complete_identity_is_required_and_injective(self):
        name = "trainverify.runtime_source_authority"
        self.assertIsNotNone(importlib.util.find_spec(name), "missing full-identity exporter")
        api = importlib.import_module(name)
        base = dict(world="p", runtime_rank=0, microbatch=0, source_tid=195, version=1)
        refs = [base] + [dict(base, **{k: v}) for k, v in
                         [("world", "s"), ("runtime_rank", 2), ("microbatch", 1),
                          ("source_tid", 432), ("version", 2)]]
        ids = [api.tensor_export_id(ref) for ref in refs]
        self.assertEqual(len(ids), len(set(ids)))
        self.assertEqual(ids, [api.tensor_export_id(dict(reversed(list(r.items())))) for r in refs])
        for field in base:
            with self.subTest(field=field):
                missing = dict(base)
                del missing[field]
                with self.assertRaisesRegex(ValueError, field):
                    api.tensor_export_id(missing)


def source_cells():
    """Constructed graph using the actual expanded-source classes (not a capture)."""
    import torch
    from nnscaler.ir.tensor import IRFullTensor
    from nnscaler_backend.build_graph import Cell
    from nnscaler_backend.dfg import Node, Tensor
    from verdict.graph import World, WType
    from verdict.operators import OpName
    world = World(wtype=WType.P, plan_ndevs=2, runtime_ndevs=4)
    weight = IRFullTensor((8, 4), name="weight", dtype=torch.float32).as_param()
    shard = weight.select(((0, 8), (0, 2)), (0, 1))
    cells = []
    for rank in (0, 2):
        cell = Cell(None, rank, WType.P)
        cell.node = Node("p", rank, 0, 129, "embedding")
        cell.opname = OpName.FW_embedding
        cell.inputs = [Tensor("p", rank, 0, 195, 1),
                       Tensor("p", rank, -1, shard.tid, 0)]
        cell.outputs = [Tensor("p", rank, 0, 432, 1)]
        cell._input_irs = [shard]
        cells.append(cell)
        update = Cell(None, rank, WType.P)
        update.node = Node("p", rank, 0, 130, "embedding")
        update.opname = OpName.FW_embedding
        update.inputs = [cell.outputs[0], cell.inputs[0], cell.outputs[0]]
        update.outputs = [Tensor("p", rank, 0, 432, 2)]
        cells.append(update)
    return world, cells, shard


class ExpandedSourceTests(unittest.TestCase):
    def test_transport_fly_rank_identity_from_actual_source_passes(self):
        from nnscaler.ir.adapter.prim import MovePrim, BroadcastPrim
        from nnscaler_backend.build_graph import (
            Cell, _set_dataflow_partial_SSA_wo_version, _set_tensor_version_to_enforce_SSA)
        from nnscaler_backend.dfg import Node
        from verdict.graph import WType
        from verdict.operators import OpName
        from nnscaler_backend.runtime_source_authority import export_expanded_cells
        from trainverify.runtime_source_authority import validate_snapshot
        world, _, shard = source_cells()
        for prim_type, src, receivers in ((MovePrim, 0, [1]), (MovePrim, 2, [3]),
                                          (BroadcastPrim, 2, [3, 0, 1])):
            with self.subTest(primitive=prim_type.__name__, src=src):
                cells = []
                for rank in [src] + receivers:
                    ins, outs = ([shard], []) if rank == src else ([], [shard])
                    kw = dict(shape=(8, 2), dtype="torch.float32", src=src)
                    kw.update(dst=receivers[0]) if prim_type is MovePrim else kw.update(ranks=[src]+receivers)
                    cell = Cell(prim_type(ins, outs, **kw), rank, WType.P)
                    cell.node = Node("p", rank, 0, 123, prim_type.__name__)
                    cell.opname = getattr(OpName, prim_type.__name__)
                    cell._input_irs, cell._output_irs = ins, outs
                    _set_dataflow_partial_SSA_wo_version([cell])
                    _set_tensor_version_to_enforce_SSA([cell])
                    cells.append(cell)
                self.assertEqual(cells[0].outputs[0].rank, -1-src)
                snapshot = export_expanded_cells(world, cells)
                validate_snapshot(snapshot)
                fly = next(t for t in snapshot["tensors"] if t["ref"]["runtime_rank"] == -1-src)
                self.assertEqual(fly["writer"], snapshot["writers"][0]["export_id"])
                self.assertEqual(fly["ref"]["version"], 0)
                for writer in snapshot["writers"][1:]:
                    self.assertEqual(writer["inputs"], [fly["ref"]])
                from copy import deepcopy
                from trainverify.runtime_source_authority import build_snapshot
                bad_writers = deepcopy(snapshot["writers"])
                bad_writers[0]["transport"]["destinations"] = [10]
                with self.assertRaisesRegex(ValueError, "transport.*producer"):
                    build_snapshot(bad_writers)
                for change in ("fly_rank", "fly_version", "missing_source", "wrong_op"):
                    bad_writers = deepcopy(snapshot["writers"])
                    sender = bad_writers[0]
                    if change == "fly_rank":
                        sender["outputs"][0]["runtime_rank"] = -100
                    elif change == "fly_version":
                        sender["outputs"][0]["version"] = 1
                    elif change == "missing_source":
                        del sender["transport"]
                    else:
                        sender["ref"]["op"] = "FW_embedding"
                    with self.subTest(change=change), self.assertRaises(ValueError):
                        build_snapshot(bad_writers)

    def test_capture_entrypoint_exists(self):
        from nnscaler_backend import runtime_source_authority as adapter
        self.assertTrue(callable(getattr(adapter, "load_capture", None)),
                        "missing real capture load/expand adapter")

    def test_snapshot_rejects_missing_refs_and_inconsistent_links(self):
        from nnscaler_backend.runtime_source_authority import export_expanded_cells
        from trainverify import runtime_source_authority as api
        from copy import deepcopy
        world, cells, _ = source_cells()
        snapshot = export_expanded_cells(world, cells)
        self.assertTrue(hasattr(api, "validate_snapshot"), "missing source-link validator")
        api.validate_snapshot(snapshot)
        mutations = []
        for section in ("tensors", "writers"):
            for field in snapshot[section][0]["ref"]:
                bad = deepcopy(snapshot)
                del bad[section][0]["ref"][field]
                mutations.append(bad)
        for direction in ("inputs", "outputs"):
            for field in snapshot["writers"][0][direction][0]:
                bad = deepcopy(snapshot)
                del bad["writers"][0][direction][0][field]
                mutations.append(bad)
        bad = deepcopy(snapshot)
        next(t for t in bad["tensors"] if t["writer"] is not None)["writer"] = None
        mutations.append(bad)
        bad = deepcopy(snapshot)
        bad["writers"].append(deepcopy(bad["writers"][0]))
        mutations.append(bad)
        bad = deepcopy(snapshot)
        bad["writers"][0]["inputs"][0]["version"] = 999
        mutations.append(bad)
        bad = deepcopy(snapshot)
        bad["tensors"][1]["export_id"] = bad["tensors"][0]["export_id"]
        mutations.append(bad)
        bad = deepcopy(snapshot)
        bad["proof_admissible"] = True
        mutations.append(bad)
        bad = deepcopy(snapshot)
        bad["writers"][0]["outputs"][0]["microbatch"] = 9
        mutations.append(bad)
        for index, bad in enumerate(mutations):
            with self.subTest(mutation=index):
                with self.assertRaises(ValueError):
                    api.validate_snapshot(bad)

    def test_reject_duplicate_writer_and_collapsed_source_outputs(self):
        from nnscaler_backend.runtime_source_authority import export_expanded_cells
        from copy import deepcopy
        world, cells, _ = source_cells()
        bad_cases = []
        bad_cases.append(cells + [cells[0]])
        no_outputs = deepcopy(cells[0])
        no_outputs.outputs = []
        bad_cases.append([no_outputs, no_outputs])
        rank_collapse = deepcopy(cells)
        rank_collapse[2].outputs = [rank_collapse[0].outputs[0]]
        bad_cases.append(rank_collapse)
        version_collapse = deepcopy(cells)
        version_collapse[1].outputs = [version_collapse[0].outputs[0]]
        bad_cases.append(version_collapse)
        for bad in bad_cases:
            with self.subTest(case=bad_cases.index(bad)):
                with self.assertRaisesRegex(ValueError, "duplicate writer|output owner"):
                    export_expanded_cells(world, bad)

    def test_actual_classes_preserve_rank_version_order_and_parameter_placement(self):
        name = "nnscaler_backend.runtime_source_authority"
        world, cells, shard = source_cells()
        self.assertIsNotNone(importlib.util.find_spec(name), "missing expanded-source adapter")
        adapter = importlib.import_module(name)
        snapshot = adapter.export_expanded_cells(world, cells)
        self.assertEqual(snapshot["scope"], "source-only")
        self.assertIs(snapshot["proof_admissible"], False)
        self.assertNotIn("batch_authority", snapshot)
        self.assertEqual(snapshot, adapter.export_expanded_cells(world, cells))
        tensors = snapshot["tensors"]
        for tid, count in ((195, 2), (432, 4)):
            selected = [t for t in tensors if t["ref"]["source_tid"] == tid]
            self.assertEqual(len(selected), count)
            self.assertEqual(len({t["export_id"] for t in selected}), count)
        for writer, cell in zip(snapshot["writers"], cells):
            self.assertEqual(writer["ref"]["source_cid"], cell.node.cid)
            self.assertEqual(writer["ref"]["runtime_rank"], cell.rank)
            self.assertEqual(writer["ref"]["microbatch"], cell.node.mb)
            self.assertEqual(writer["ref"]["op"], cell.opname.name)
            self.assertEqual([r["source_tid"] for r in writer["inputs"]], [t.tid for t in cell.inputs])
            self.assertEqual([r["version"] for r in writer["outputs"]], [t.v for t in cell.outputs])
        params = [t for t in tensors if "placement" in t]
        self.assertEqual(len(params), 2)
        self.assertEqual([p["placement"]["scale_unit"] for p in params], [0, 1])
        for p in params:
            self.assertEqual(p["placement"]["parent_tid"], shard.parent.tid)
            self.assertEqual(p["placement"]["indmap"], [[0, 8], [0, 2]])
            self.assertEqual(p["placement"]["full_shape"], [8, 4])


if __name__ == "__main__":
    unittest.main()
