"""Tests of `merge_parity.py` on shard counts written here."""

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Load the script by path: `scripts` is not a package.
spec = importlib.util.spec_from_file_location("merge_parity", HERE / "merge_parity.py")
assert spec and spec.loader
merge = importlib.util.module_from_spec(spec)
spec.loader.exec_module(merge)

ROW = "execution-spec-tests - Osaka state_test"
CATALOGUE = {ROW: {"rank": 17, "cases": 5, "runnable": 4, "plan": "later"}}


def shard(passed: int, failed: int = 0, catalogue: dict | None = None) -> dict:
    """The counts of one shard."""
    return {
        "catalogue": catalogue or CATALOGUE,
        "outcomes": {ROW: {"passed": passed, "failed": failed}},
    }


class Merge(unittest.TestCase):
    def run_merge(self, *shards: dict) -> tuple[int, str]:
        """The exit code and the merged report of the shards."""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paths = []
            for index, counts in enumerate(shards):
                path = root / f"{index}.json"
                path.write_text(json.dumps(counts))
                paths.append(str(path))
            output = root / "parity.md"
            code = merge.main([str(output), *paths])
            return code, output.read_text() if output.exists() else ""

    def test_shards_that_run_each_case_once_merge(self):
        code, text = self.run_merge(shard(3), shard(0, failed=1))
        self.assertEqual(code, 0)
        self.assertIn("| - | Osaka | state_test | 5 | 3 | 0 | 1 | 1 | 60.0 % | later |", text)

    def test_a_missing_case_fails(self):
        self.assertEqual(
            merge.report.merge([shard(2), shard(1)]), [f"{ROW}: 3 outcomes for 4 runnable cases"]
        )

    def test_a_case_run_twice_fails(self):
        self.assertEqual(
            merge.report.merge([shard(3), shard(2)]), [f"{ROW}: 5 outcomes for 4 runnable cases"]
        )

    def test_shards_of_different_catalogues_fail(self):
        other = {ROW: {**CATALOGUE[ROW], "runnable": 3}}
        problems = merge.report.merge([shard(3), shard(1, catalogue=other)])
        self.assertIn("the shards hold different catalogues", problems)

    def test_no_shard_fails(self):
        self.assertEqual(self.run_merge(), (1, ""))


if __name__ == "__main__":
    unittest.main()
