"""Dependency-light unit tests; synthetic source is NOT upstream evidence.

Optional actual-source matrix:
TV_TOPOLOGY_UPSTREAM=/trusted/repo TV_TOPOLOGY_REVISION=<full commit> \
    python -m unittest discover -s scripts/tests -p test_parallel_topology.py -v
"""
import importlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest
from dataclasses import FrozenInstanceError, replace
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
REVISION = "a" * 40
# Deliberately small synthetic source for unit isolation, not an upstream copy.
UNIT_SOURCE = '''
def resolve_parallel_sizes(args, plan_ngpus):
    args.cp_size = args.cp_size or (1 if args.dp_sharded else plan_ngpus)
    args.ep_size = args.ep_size or plan_ngpus

def validate_pipeline_compatibility(args, pivots):
    if not args.dp_sharded and args.cp_size < args.ep_size and pivots:
        raise ValueError("pipeline incompatible")

def get_data_lane_group(runtime_rank, plan_ngpus, cp_size):
    start = runtime_rank // plan_ngpus * plan_ngpus
    return tuple(range(start + runtime_rank % cp_size, start + plan_ngpus, cp_size))

def build_runtime_process_groups(runtime_ngpus, plan_ngpus, cp_size, ep_size):
    groups = set()
    for rank in range(runtime_ngpus):
        base = rank // plan_ngpus * plan_ngpus
        for width in (plan_ngpus, cp_size, ep_size):
            start = base + (rank - base) // width * width
            groups.add(tuple(range(start, start + width)))
        groups.add(get_data_lane_group(rank, plan_ngpus, cp_size))
    return sorted(group for group in groups if len(group) > 1)
'''


def fake_git(command, **kwargs):
    output = "commit\n" if "cat-file" in command else UNIT_SOURCE
    return subprocess.CompletedProcess(command, 0, output, "")


class TopologyTests(unittest.TestCase):
    def setUp(self):
        self.assertIsNotNone(importlib.util.find_spec("trainverify.parallel_topology"),
                             "parallel topology feature is missing")
        self.api = importlib.import_module("trainverify.parallel_topology")

    def derive(self, **kwargs):
        with patch("subprocess.run", side_effect=fake_git):
            return self.api.derive_topology(self.api.ParallelConfig(**kwargs),
                                           upstream_root="/unit/mock-upstream", revision=REVISION)

    def test_source_derived_equal_family_and_rank_api(self):
        for k in (1, 3, 5):
            with self.subTest(k=k):
                topology = self.derive(plan_ngpus=k, runtime_ngpus=k)
                self.assertEqual(topology.config.cp_size, k)
                self.assertEqual(topology.config.ep_size, k)
                self.assertEqual(topology.config.zero_group_size, k)
                self.assertEqual(topology.source_revision, REVISION)
                self.assertEqual(topology.evidence_kind, "source-derived-topology")
                self.assertEqual(topology.eager_groups, (tuple(range(k)),) if k > 1 else ())
                for role in ("scale_unit", "cp", "ep"):
                    self.assertEqual(topology.groups_for(role),
                                     (self.api.ParallelGroup(role, 0, tuple(range(k))),))
                    for rank in range(k):
                        self.assertEqual(topology.local_rank(role, rank), rank)
                self.assertEqual(tuple(g.members for g in topology.groups_for("data_lane")),
                                 tuple((rank,) for rank in range(k)))
                self.api.validate_topology(topology)
                with self.assertRaises(FrozenInstanceError):
                    topology.config.cp_size = 1


    def test_json_roundtrip_strict_schema_and_evidence(self):
        self.assertTrue(callable(getattr(self.api, "topology_to_dict", None)), "JSON export feature is missing")
        topology = self.derive(plan_ngpus=8, runtime_ngpus=16, cp_size=4, ep_size=8)
        payload = self.api.topology_to_dict(topology)
        self.assertEqual(self.api.topology_from_dict(json.loads(json.dumps(payload))), topology)
        self.assertEqual(payload["source_revision"], REVISION)
        mutations = []
        for key in ("unknown", "observed_runtime", "lean_proof"):
            bad = json.loads(json.dumps(payload))
            bad[key] = True
            mutations.append(bad)
        for field in payload:
            bad = json.loads(json.dumps(payload))
            del bad[field]
            mutations.append(bad)
        for location in ("config", "groups"):
            bad = json.loads(json.dumps(payload))
            target = bad[location] if location == "config" else bad[location][0]
            target["extra"] = 1
            mutations.append(bad)
        for kind in ("observed-runtime", "Leanproof", 1):
            bad = json.loads(json.dumps(payload))
            bad["evidence_kind"] = kind
            mutations.append(bad)
        for field, value in (("cp_size", True), ("dp_sharded", 0), ("cp_size", 0),
                             ("zero_group_size", None), ("plan_ngpus", 8.0)):
            bad = json.loads(json.dumps(payload))
            bad["config"][field] = value
            mutations.append(bad)
        for field, value in (("scale_unit", False), ("members", [False, 1]), ("role", "zero")):
            bad = json.loads(json.dumps(payload))
            bad["groups"][0][field] = value
            mutations.append(bad)
        for field in ("groups", "eager_groups"):
            bad = json.loads(json.dumps(payload))
            bad[field] = tuple(bad[field])
            mutations.append(bad)
        for bad in mutations:
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                self.api.topology_from_dict(bad)

    def test_nested_families_exact_members_not_cartesian(self):
        for cp, ep, dp in ((8, 4, False), (4, 8, False), (1, 8, True)):
            topology = self.derive(plan_ngpus=8, runtime_ngpus=16, cp_size=cp,
                                   ep_size=ep, dp_sharded=dp, moe_expert_num=16)
            with self.subTest(cp=cp, ep=ep, dp=dp):
                for unit in (0, 1):
                    base = unit * 8
                    self.assertEqual(topology.group_for_rank("scale_unit", base).members,
                                     tuple(range(base, base + 8)))
                    for role, width in (("cp", cp), ("ep", ep)):
                        self.assertEqual(tuple(g.members for g in topology.groups_for(role) if g.scale_unit == unit),
                                         tuple(tuple(range(base + i, base + i + width)) for i in range(0, 8, width)))
                    self.assertEqual(tuple(g.members for g in topology.groups_for("data_lane") if g.scale_unit == unit),
                                     tuple(tuple(range(base + i, base + 8, cp)) for i in range(cp)))
                self.assertEqual(topology.local_rank("data_lane", 15), 7 // cp)
                self.api.validate_topology(topology)

    def test_legal_auto_sentinels_and_zero_defaults(self):
        for cp, ep, dp, expected in ((0, 0, False, (8, 8)), (0, 4, False, (8, 4)),
                                      (4, 0, False, (4, 8)), (0, 0, True, (1, 8)),
                                      (0, 1, True, (1, 1))):
            topology = self.derive(plan_ngpus=8, runtime_ngpus=16, cp_size=cp, ep_size=ep, dp_sharded=dp)
            self.assertEqual((topology.config.cp_size, topology.config.ep_size), expected)
            self.assertEqual(topology.config.zero_group_size, 16)
        self.assertEqual(self.derive(plan_ngpus=8, runtime_ngpus=16, zero_group_size=8).config.zero_group_size, 8)
        self.derive(plan_ngpus=8, runtime_ngpus=16, cp_size=8, ep_size=4, pipeline_stages=2)
        self.derive(plan_ngpus=8, runtime_ngpus=16, dp_sharded=True, pipeline_stages=2)

    def test_invalid_divisibility_experts_pipeline_and_zero(self):
        for changes in ({"runtime_ngpus": 12}, {"cp_size": 3}, {"ep_size": 3},
                        {"cp_size": 4, "ep_size": 4}, {"cp_size": 8, "dp_sharded": True},
                        {"moe_expert_num": 7}, {"moe_expert_num": 0},
                        {"zero_group_size": 0}, {"zero_group_size": 3}, {"zero_group_size": 4},
                        {"zero_group_size": 32}, {"pipeline_stages": 0},
                        {"cp_size": 4, "ep_size": 8, "pipeline_stages": 2}):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                self.derive(**({"plan_ngpus": 8, "runtime_ngpus": 16} | changes))

    def test_negative_bool_and_noninteger_fields(self):
        for name in ("plan_ngpus", "runtime_ngpus", "cp_size", "ep_size", "moe_expert_num", "zero_group_size", "pipeline_stages"):
            for value in (-1, True, False, 1.0, "1"):
                with self.subTest(name=name, value=value), self.assertRaises(ValueError):
                    self.derive(**({"plan_ngpus": 8, "runtime_ngpus": 16} | {name: value}))
        for value in (-1, 0, 1, None, "False"):
            with self.subTest(dp=value), self.assertRaises(ValueError):
                self.derive(plan_ngpus=8, runtime_ngpus=16, dp_sharded=value)

    def test_gqa_is_not_a_topology_field_or_constraint(self):
        topology = self.derive(plan_ngpus=3, runtime_ngpus=3)
        self.api.validate_topology(topology)
        with self.assertRaises(TypeError):
            self.api.ParallelConfig(plan_ngpus=3, runtime_ngpus=3, n_kv_heads=2)

    def test_revision_validated_before_lookup_and_preserved(self):
        for revision in ("HEAD", "a" * 39, "g" * 40, REVISION + "\n", " " + REVISION, 1):
            with patch("subprocess.run") as run, self.assertRaises(ValueError):
                self.api.derive_topology(self.api.ParallelConfig(1, 1), upstream_root="/unit", revision=revision)
            run.assert_not_called()
        with patch("subprocess.run", side_effect=fake_git) as run:
            topology = self.api.derive_topology(self.api.ParallelConfig(1, 1), upstream_root="/unit", revision="B" * 40)
        self.assertEqual(topology.source_revision, "B" * 40)
        self.assertIn(["git", "-C", "/unit", "show", "B" * 40 + ":llm/parallelism.py"],
                      [call.args[0] for call in run.call_args_list])
        with patch("subprocess.run", return_value=subprocess.CompletedProcess([], 0, "tree\n", "")), self.assertRaises(ValueError):
            self.api.derive_topology(self.api.ParallelConfig(1, 1), upstream_root="/unit", revision=REVISION)

    def test_source_lane_and_eager_disagreement_rejected(self):
        for addition in ("\ndef get_data_lane_group(*args): return (0,)\n",
                         "\ndef build_runtime_process_groups(*args): return []\n",
                         "\ndef build_runtime_process_groups(*args): return [(1,0)]\n"):
            def git(command, **kwargs):
                value = "commit\n" if "cat-file" in command else UNIT_SOURCE + addition
                return subprocess.CompletedProcess(command, 0, value, "")
            with patch("subprocess.run", side_effect=git), self.assertRaises(ValueError):
                self.api.derive_topology(self.api.ParallelConfig(8, 16, 4, 8), upstream_root="/unit", revision=REVISION)

    def test_coordinated_same_total_topology_mutations_rejected(self):
        topology = self.derive(plan_ngpus=8, runtime_ngpus=16, cp_size=4, ep_size=8)
        original = topology.groups
        transforms = (
            lambda g: replace(g, role={"cp": "data_lane", "data_lane": "cp"}.get(g.role, g.role)),
            lambda g: replace(g, members=tuple(reversed(g.members))),
            lambda g: replace(g, members=tuple((r + 1) % 16 for r in g.members)),
            lambda g: replace(g, members=tuple((r + 8) % 16 for r in g.members)),
            lambda g: replace(g, scale_unit=1 - g.scale_unit),
        )
        for transform in transforms:
            groups = tuple(transform(g) for g in original)
            groups = tuple(sorted(groups, key=lambda g: (g.scale_unit, ("scale_unit", "cp", "ep", "data_lane").index(g.role), g.members[0])))
            eager = tuple(sorted({g.members for g in groups if len(g.members) > 1}))
            mutated = replace(topology, groups=groups, eager_groups=eager)
            self.assertEqual(sum(len(g.members) for g in original), sum(len(g.members) for g in groups))
            with self.subTest(transform=transform), self.assertRaises(ValueError):
                self.api.validate_topology(mutated)
        # Same role-row census, noncanonical row order.
        for groups in (tuple(reversed(original)), original[:-1], original + (original[0],)):
            with self.assertRaises(ValueError):
                self.api.validate_topology(replace(topology, groups=groups))
        for eager in (tuple(reversed(topology.eager_groups)), topology.eager_groups + ((0,),), topology.eager_groups[:-1]):
            with self.assertRaises(ValueError):
                self.api.validate_topology(replace(topology, eager_groups=eager))

    def test_rank_api_rejects_unknown_invalid_and_nonunique(self):
        topology = self.derive(plan_ngpus=3, runtime_ngpus=3)
        for rank in (-1, 3, True, 1.0):
            with self.assertRaises(ValueError):
                topology.local_rank("cp", rank)
        with self.assertRaises(ValueError):
            topology.groups_for("zero")
        duplicate = replace(topology, groups=topology.groups + topology.groups_for("cp"))
        with self.assertRaises(ValueError):
            duplicate.group_for_rank("cp", 0)

    def test_validator_independent_of_emitter_and_config_metadata(self):
        topology = self.derive(plan_ngpus=8, runtime_ngpus=16, cp_size=4, ep_size=8)
        with patch.object(self.api, "_semantic_groups", side_effect=AssertionError("validator called emitter")):
            self.api.validate_topology(topology)
            for changes in ({"cp_size": 2}, {"cp_size": 8, "ep_size": 4},
                            {"plan_ngpus": 16}, {"runtime_ngpus": 8},
                            {"cp_size": 0}, {"zero_group_size": None},
                            {"zero_group_size": 4}, {"moe_expert_num": 7},
                            {"pipeline_stages": 2}, {"dp_sharded": True}):
                with self.subTest(changes=changes), self.assertRaises(ValueError):
                    self.api.validate_topology(replace(topology, config=replace(topology.config, **changes)))
        with self.assertRaises(FrozenInstanceError):
            topology.source_revision = "b" * 40
        with self.assertRaises(FrozenInstanceError):
            topology.groups[0].scale_unit = 3


@unittest.skipUnless(os.environ.get("TV_TOPOLOGY_UPSTREAM"), "actual-source probe requires explicit trusted repository")
class ActualPinnedSourceTests(unittest.TestCase):
    def test_pinned_source_configuration_matrix(self):
        api = importlib.import_module("trainverify.parallel_topology")
        root = os.environ["TV_TOPOLOGY_UPSTREAM"]
        revision = os.environ["TV_TOPOLOGY_REVISION"]
        cases = [api.ParallelConfig(k, k) for k in (1, 3, 5)]
        cases += [api.ParallelConfig(8, r, cp, ep, dp, 16)
                  for r in (8, 16) for cp, ep, dp in ((8, 4, False), (4, 8, False), (1, 8, True))]
        cases += [api.ParallelConfig(8, 16, 0, 0, dp) for dp in (False, True)]
        cases += [api.ParallelConfig(8, 16, 8, 4, False, 16, 8, 2)]
        for config in cases:
            with self.subTest(config=config):
                topology = api.derive_topology(config, upstream_root=root, revision=revision)
                api.validate_topology(topology)
                self.assertEqual(api.topology_from_dict(api.topology_to_dict(topology)), topology)
                self.assertEqual(topology.source_revision, revision)
                self.assertEqual({g.role for g in topology.groups}, {"scale_unit", "cp", "ep", "data_lane"})
        invalid = [api.ParallelConfig(8, 12), api.ParallelConfig(8, 16, 3, 8),
                   api.ParallelConfig(8, 16, 4, 8, False, 7),
                   api.ParallelConfig(8, 16, 4, 8, False, 16, None, 2),
                   api.ParallelConfig(8, 16, 8, 4, False, 16, 4)]
        for config in invalid:
            with self.subTest(invalid=config), self.assertRaises(ValueError):
                api.derive_topology(config, upstream_root=root, revision=revision)
        print(f"actual pinned source: {len(cases)} accepted, {len(invalid)} rejected at {revision}")


if __name__ == "__main__":
    unittest.main()
