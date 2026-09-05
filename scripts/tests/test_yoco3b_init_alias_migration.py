from __future__ import annotations

import hashlib
import importlib.util
import pathlib
import re
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/authority_migrations/yoco3b/03_init_alias.py"
REPLICA_GROUP_SCRIPT = ROOT / "scripts/authority_migrations/yoco3b/04_attention_replica_groups.py"
HEARTBEAT_SCRIPT = ROOT / "scripts/authority_migrations/yoco3b/05_heartbeat_budget.py"
REDUCE_SCATTER_SCRIPT = ROOT / "scripts/authority_migrations/yoco3b/02_reduce_scatter.py"
RESHAPE_SCRIPT = ROOT / "scripts/authority_migrations/yoco3b/01_reshape.py"
AUTHORITY = ROOT / "trainverify/denote/GeneratedYOCO3B.lean"


def load_script(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def stage4_source():
    migration = load_script(HEARTBEAT_SCRIPT, "yoco3b_heartbeat_stage4_helper")
    source = AUTHORITY.read_text()
    if source.count(migration.NEW) != 1 or migration.OLD in source:
        raise AssertionError("current authority lacks exact stage-5 heartbeat policy")
    source = source.replace(migration.NEW, migration.OLD, 1)
    if hashlib.sha256(source.encode()).hexdigest() != migration.INPUT_SHA256:
        raise AssertionError("reconstructed stage-4 digest mismatch")
    return source


def stage3_source():
    source = stage4_source()
    legacy = "  refine { numRanks := 2, nodes := ?_ }"
    source, count = re.subn(
        r"(?m)^  refine \{ numRanks := 2, nodes := \?_, replicaGroups := \[.*\] \}$",
        legacy,
        source,
        count=1,
    )
    if count != 1:
        raise AssertionError("current authority lacks one exact PM replicaGroups field")
    if hashlib.sha256(source.encode()).hexdigest() != load_script(
        REPLICA_GROUP_SCRIPT, "yoco3b_replica_groups_stage3_helper"
    ).INPUT_SHA256:
        raise AssertionError("reconstructed stage-3 digest mismatch")
    return source


class YOCO3BHeartbeatMigrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.migration = load_script(HEARTBEAT_SCRIPT, "yoco3b_heartbeat_migration")
        cls.current = AUTHORITY.read_text()
        cls.stage4 = stage4_source()

    def test_exact_transform_and_idempotence(self):
        output, changed = self.migration.transform(self.stage4)
        self.assertEqual(changed, 1)
        self.assertEqual(output, self.current)
        again, changed_again = self.migration.transform(output)
        self.assertEqual(changed_again, 0)
        self.assertEqual(again, output)

    def test_mixed_policy_rejected(self):
        mixed = self.current + "\n" + self.migration.OLD
        with self.assertRaisesRegex(RuntimeError, "mixed or malformed"):
            self.migration.transform(mixed)


class YOCO3BReplicaGroupMigrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.migration = load_script(REPLICA_GROUP_SCRIPT, "yoco3b_replica_groups_migration")
        cls.final_source = stage4_source()
        cls.stage3_source = stage3_source()

    def test_exact_transform_and_idempotence(self):
        output, changed = self.migration.validate_and_transform(self.stage3_source)
        self.assertEqual(changed, 42)
        self.assertEqual(output, self.final_source)
        self.assertEqual(hashlib.sha256(output.encode()).hexdigest(), self.migration.OUTPUT_SHA256)
        again, changed_again = self.migration.validate_and_transform(output)
        self.assertEqual(changed_again, 0)
        self.assertEqual(again, output)

    def test_duplicate_pm_rank_is_rejected(self):
        corrupted = self.stage3_source.replace(
            'rank := 1, op := "OpName.FW_maybe_shuffle"',
            'rank := 0, op := "OpName.FW_maybe_shuffle"',
            1,
        )
        with self.assertRaisesRegex(RuntimeError, "PM rank cardinality|collective parameters/signature|duplicate PM rank"):
            self.migration.validate_and_transform(corrupted)

    def test_orphan_attention_signature_is_rejected(self):
        corrupted = self.stage3_source.replace(
            'rank := 1, op := "OpName.FW_attn_sliding_window", ins := [9884, 9886, 9864, 6304, 6305]',
            'rank := 1, op := "OpName.FW_attn_sliding_window", ins := [9884, 9886, 9864, 6304, 999999]',
            1,
        )
        with self.assertRaisesRegex(RuntimeError, "rank-pair logical signatures disagree"):
            self.migration.validate_and_transform(corrupted)

    def test_coordinated_rank1_metadata_permutation_is_rejected(self):
        lines = self.stage3_source.splitlines(keepends=True)
        indices = [i for i, line in enumerate(lines)
                   if 'rank := 1, op := "OpName.FW_attn_sliding_window"' in line]
        self.assertGreaterEqual(len(indices), 2)
        first, second = indices[:2]
        pattern = re.compile(r"(ins := \[[0-9, ]+, )([0-9]+), ([0-9]+)(\], outs)")
        one, two = pattern.search(lines[first]), pattern.search(lines[second])
        self.assertIsNotNone(one); self.assertIsNotNone(two)
        pair1, pair2 = one.group(2, 3), two.group(2, 3)
        lines[first] = pattern.sub(rf"\g<1>{pair2[0]}, {pair2[1]}\g<4>", lines[first], count=1)
        lines[second] = pattern.sub(rf"\g<1>{pair1[0]}, {pair1[1]}\g<4>", lines[second], count=1)
        with self.assertRaisesRegex(RuntimeError, "rank-pair logical signatures disagree"):
            self.migration.validate_and_transform("".join(lines))

    def test_coordinated_rank1_payload_permutation_is_rejected(self):
        lines = self.stage3_source.splitlines(keepends=True)
        indices = [i for i, line in enumerate(lines)
                   if 'rank := 1, op := "OpName.FW_attn_sliding_window"' in line]
        first, second = indices[:2]
        pattern = re.compile(
            r"(ins := \[)([0-9]+), ([0-9]+), ([0-9]+)(, [0-9]+, [0-9]+\], outs := \[)([0-9]+)(\])"
        )
        one, two = pattern.search(lines[first]), pattern.search(lines[second])
        self.assertIsNotNone(one); self.assertIsNotNone(two)
        payload1, payload2 = one.group(2, 3, 4, 6), two.group(2, 3, 4, 6)
        lines[first] = pattern.sub(
            rf"\g<1>{payload2[0]}, {payload2[1]}, {payload2[2]}\g<5>{payload2[3]}\g<7>",
            lines[first], count=1,
        )
        lines[second] = pattern.sub(
            rf"\g<1>{payload1[0]}, {payload1[1]}, {payload1[2]}\g<5>{payload1[3]}\g<7>",
            lines[second], count=1,
        )
        with self.assertRaisesRegex(RuntimeError, "rank-local TID pairing disagrees"):
            self.migration.validate_and_transform("".join(lines))

    def test_partial_metadata_is_rejected(self):
        partial = self.stage3_source.replace(
            "  refine { numRanks := 2, nodes := ?_ }",
            "  refine { numRanks := 2, nodes := ?_, replicaGroups := [] }",
            1,
        )
        with self.assertRaisesRegex(RuntimeError, "partial or foreign"):
            self.migration.validate_and_transform(partial)


class YOCO3BInitAliasMigrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.migration = load_script(SCRIPT, "yoco3b_init_alias_migration")
        cls.final_source = stage3_source()
        source = cls.final_source
        for ts, piece in cls.migration.EXPECTED.items():
            new = f"tps := [{{ rank := 0, tid := {ts} }}]"
            old = f"tps := [{{ rank := 0, tid := {piece} }}]"
            if source.count(new) != 1:
                raise AssertionError(f"current authority lacks exact migrated initGoal_{ts}")
            source = source.replace(new, old, 1)
        cls.stage2_source = source
        digest = hashlib.sha256(source.encode()).hexdigest()
        if digest != cls.migration.INPUT_SHA256:
            raise AssertionError(f"reconstructed stage-2 digest mismatch: {digest}")

    def test_historical_exact_set_and_byte_output(self):
        output, replacements = self.migration.validate_and_transform(self.stage2_source)
        self.assertEqual(replacements, self.migration.EXPECTED)
        self.assertEqual(output, self.final_source)
        self.assertEqual(
            hashlib.sha256(output.encode()).hexdigest(),
            self.migration.OUTPUT_SHA256,
        )

    def test_idempotent_current_output(self):
        output, replacements = self.migration.validate_and_transform(self.final_source)
        self.assertEqual(replacements, {})
        self.assertEqual(output, self.final_source)

    def test_matching_rank_producer_mutation_is_rejected(self):
        lines = self.stage2_source.splitlines(keepends=True)
        matches = [
            index for index, line in enumerate(lines)
            if "rank := 0" in line
            and 'op := "OpName.FW_multiref"' in line
            and "15935" in line.partition("outs :=")[2].partition("]")[0]
        ]
        self.assertEqual(len(matches), 1)
        index = matches[0]
        lines[index] = lines[index].replace(
            "OpName.FW_multiref", "OpName.FW_view", 1
        )
        with self.assertRaisesRegex(RuntimeError, "producer identity is malformed"):
            self.migration.validate_and_transform("".join(lines))

    def test_unexpected_expected_pair_is_rejected(self):
        corrupted = self.stage2_source.replace(
            "tps := [{ rank := 0, tid := 15935 }]",
            "tps := [{ rank := 0, tid := 15936 }]",
            1,
        )
        with self.assertRaisesRegex(RuntimeError, "expected rank-0 piece"):
            self.migration.validate_and_transform(corrupted)


class YOCO3BReduceScatterMigrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.stage3 = load_script(SCRIPT, "yoco3b_init_alias_for_rs_tests")
        cls.stage2 = load_script(REDUCE_SCATTER_SCRIPT, "yoco3b_reduce_scatter_migration")
        source = stage3_source()
        for ts, piece in cls.stage3.EXPECTED.items():
            source = source.replace(
                f"tps := [{{ rank := 0, tid := {ts} }}]",
                f"tps := [{{ rank := 0, tid := {piece} }}]",
                1,
            )
        cls.stage2_source = source
        stage1 = source
        for old, new in cls.stage2.REPLACEMENTS:
            if stage1.count(new) != 1:
                raise AssertionError(f"stage-2 authority lacks exact record: {new}")
            stage1 = stage1.replace(new, old, 1)
        cls.stage1_source = stage1
        if hashlib.sha256(stage1.encode()).hexdigest() != cls.stage2.INPUT_SHA256:
            raise AssertionError("reconstructed stage-1 hash mismatch")

    def test_exact_transform_and_idempotence(self):
        output, changed = self.stage2.transform(self.stage1_source)
        self.assertEqual(changed, 2)
        self.assertEqual(output, self.stage2_source)
        again, changed_again = self.stage2.transform(output)
        self.assertEqual(changed_again, 0)
        self.assertEqual(again, output)

    def test_mixed_stage_rejected(self):
        old, new = self.stage2.REPLACEMENTS[0]
        mixed = self.stage1_source.replace(old, new, 1)
        with self.assertRaisesRegex(RuntimeError, "mixed or malformed"):
            self.stage2.transform(mixed)


class YOCO3BReshapeMigrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        stage3 = load_script(SCRIPT, "yoco3b_init_alias_for_reshape_tests")
        stage2 = load_script(REDUCE_SCATTER_SCRIPT, "yoco3b_rs_for_reshape_tests")
        cls.stage1 = load_script(RESHAPE_SCRIPT, "yoco3b_reshape_migration")
        source = stage3_source()
        for ts, piece in stage3.EXPECTED.items():
            source = source.replace(
                f"tps := [{{ rank := 0, tid := {ts} }}]",
                f"tps := [{{ rank := 0, tid := {piece} }}]", 1,
            )
        for old, new in stage2.REPLACEMENTS:
            source = source.replace(new, old, 1)
        cls.stage1_source = source
        lines = []
        import re
        for line in source.splitlines(keepends=True):
            if "OpName.FW_reshape" in line:
                line, _count = re.subn(
                    r", params := \[[0-9, ]+\](\s*\},)", r"\1", line, count=1
                )
            lines.append(line)
        cls.stage0_source = "".join(lines)
        if hashlib.sha256(cls.stage0_source.encode()).hexdigest() != cls.stage1.INPUT_SHA256:
            raise AssertionError("reconstructed stage-0 hash mismatch")

    def test_exact_transform_and_idempotence(self):
        output, changed = self.stage1.transform(self.stage0_source)
        self.assertEqual(changed, 720)
        self.assertEqual(output, self.stage1_source)
        again, changed_again = self.stage1.transform(output)
        self.assertEqual(changed_again, 0)
        self.assertEqual(again, output)

    def test_mixed_stage_rejected(self):
        first = next(
            line for line in self.stage1_source.splitlines(keepends=True)
            if "OpName.FW_reshape" in line
        )
        import re
        legacy, count = re.subn(
            r", params := \[[0-9, ]+\](\s*\},)", r"\1", first, count=1
        )
        self.assertEqual(count, 1)
        mixed = self.stage1_source.replace(first, legacy, 1)
        with self.assertRaisesRegex(RuntimeError, "mixed reshape migration state"):
            self.stage1.transform(mixed)


if __name__ == "__main__":
    unittest.main()
