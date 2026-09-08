"""Portable synthetic feed generator tests; kernel checks are separate."""
import importlib.util
from pathlib import Path
import unittest

class InputFeedTests(unittest.TestCase):
    def generator(self):
        path = Path(__file__).with_name("gen_source_scoped_input_witness.py")
        self.assertTrue(path.exists(), "checked input feed witness generator is missing")
        spec = importlib.util.spec_from_file_location("input_witness", path)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        return mod

    def test_generated_mixed_world_and_rejections(self):
        mod = self.generator()
        for ranks in ((0, 2), (0, 2, 5)):
            text = mod.generate(ranks)
            self.assertEqual(text, mod.generate(ranks))
            for marker in ("denoteWithInputs", "mixed_read", "mixed_frame", "missing_reject",
                           "duplicate_reject", "reordered_reject", "extra_reject", "badports_reject",
                           "old_loader_blocked", "OpName.FW_add", "OpName.AllReducePrim"):
                self.assertIn(marker, text)
            self.assertIn(f"numRanks := {max(ranks) + 2}", text)
            self.assertNotIn("InitGoal", text)

    def test_invalid_rank_domains_reject(self):
        mod = self.generator()
        for ranks in ((), (0, 0), (-1, 2)):
            with self.subTest(ranks=ranks), self.assertRaises(ValueError):
                mod.generate(ranks)

    def test_value_and_source_shape_conventions(self):
        mod = self.generator()
        for ranks, shape, value in (((0, 2), [12, 8], 33), ((0, 2, 5), [18, 12], 66)):
            text = mod.generate(ranks)
            self.assertIn(f"⟨{shape}, fun _ => v⟩", text)
            self.assertIn(f"0 = {value}", text)
            self.assertIn("mixed_success", text)
            self.assertIn("mixed_missingpayload_reject", text)
            self.assertIn("mixed_badports_reject", text)
            self.assertIn("mixed_reorderedports_reject", text)

if __name__ == "__main__":
    unittest.main()
