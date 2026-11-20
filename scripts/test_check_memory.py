"""Unit tests for the classification of `scripts/check_memory.py`."""

import importlib.util
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Load the script by path: `scripts` is not a package.
spec = importlib.util.spec_from_file_location("check_memory", HERE / "check_memory.py")
assert spec and spec.loader
check_memory = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check_memory)

GIB = check_memory.GIB
classify = check_memory.classify
WARN = 2 * GIB
FAIL = 4 * GIB


class ClassifyTest(unittest.TestCase):
    """Each limit decides the result on its own, and an exit code decides it first."""

    def test_within_every_limit(self) -> None:
        self.assertEqual(classify(GIB, 5.0, 0, WARN, FAIL, 20.0), "ok")

    def test_memory_above_the_warning(self) -> None:
        self.assertEqual(classify(3 * GIB, 5.0, 0, WARN, FAIL, 20.0), "warning")

    def test_memory_above_the_failure(self) -> None:
        self.assertEqual(classify(5 * GIB, 5.0, 0, WARN, FAIL, 20.0), "failure")

    def test_cpu_above_its_limit(self) -> None:
        self.assertEqual(classify(GIB, 21.0, 0, WARN, FAIL, 20.0), "failure")

    def test_cpu_at_its_limit(self) -> None:
        self.assertEqual(classify(GIB, 20.0, 0, WARN, FAIL, 20.0), "ok")

    def test_no_cpu_limit(self) -> None:
        self.assertEqual(classify(GIB, 1000.0, 0, WARN, FAIL), "ok")

    def test_lean_error(self) -> None:
        self.assertEqual(classify(GIB, 5.0, 1, WARN, FAIL, 20.0), "error")


if __name__ == "__main__":
    unittest.main()
