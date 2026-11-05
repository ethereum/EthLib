"""Tests of `check_fork_cap.py` on small repositories in a temporary directory."""

import importlib.util
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Load the script by path: `scripts` is not a package.
spec = importlib.util.spec_from_file_location("check_fork_cap", HERE / "check_fork_cap.py")
cap = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cap)

CAPPED = """\
/-- The fork, capped. -/
@[export eth_a]
def aExport (fork bytes : ByteArray) : Result UInt8 := do
  let fork ← forkUpTo .glamsterdam fork
  pure 1
"""

THROUGH_HELPER = """\
/-- A helper that caps the fork. -/
def decodeAt (last : Fork) (fork bytes : ByteArray) : Result Fork := do
  forkUpTo last fork

@[export eth_b]
def bExport (fork bytes : ByteArray) : Result UInt8 := do
  let _ ← decodeAt .bpo5 fork bytes
  pure 1
"""

UNCAPPED = """\
@[export eth_c]
def cExport (fork topic : ByteArray) : Result ByteArray := do
  return messageId (← forkOfName fork) topic
"""

NO_READER = """\
-- `forkOfName` in a comment is not a call.
@[export eth_d]
def dExport (fork : ByteArray) : Result ByteArray := do
  return fork
"""


class CheckForkCap(unittest.TestCase):
    def run_check(self, files: dict[str, str], allowlist: str = "") -> list[str]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name, text in files.items():
                path = root / "EthLib" / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text, encoding="utf-8")
            (root / "scripts").mkdir()
            (root / cap.ALLOWLIST).write_text(allowlist, encoding="utf-8")
            return cap.check(root)

    def test_capped_export_passes(self):
        self.assertEqual(self.run_check({"X/Exports/A.lean": CAPPED}), [])

    def test_cap_through_a_helper_passes(self):
        self.assertEqual(self.run_check({"X/Exports/B.lean": THROUGH_HELPER}), [])

    def test_uncapped_reader_fails(self):
        problems = self.run_check({"X/Exports/C.lean": UNCAPPED})
        self.assertEqual(len(problems), 2)
        self.assertIn("cExport reads a fork name without a cap", problems[0])
        self.assertIn("export cExport takes a fork but never caps it", problems[1])

    def test_allowlisted_reader_passes(self):
        allowlist = "EthLib/X/Exports/C.lean cExport: the rule is the same at every fork\n"
        self.assertEqual(self.run_check({"X/Exports/C.lean": UNCAPPED}, allowlist), [])

    def test_entry_without_reason_fails(self):
        problems = self.run_check(
            {"X/Exports/C.lean": UNCAPPED}, "EthLib/X/Exports/C.lean cExport:\n"
        )
        self.assertTrue(any("path name: reason" in p for p in problems))

    def test_stale_entry_fails(self):
        problems = self.run_check(
            {"X/Exports/A.lean": CAPPED}, "EthLib/X/Exports/A.lean aExport: no longer needed\n"
        )
        self.assertEqual(len(problems), 1)
        self.assertIn("remove the entry", problems[0])

    def test_export_with_a_fork_and_no_cap_fails(self):
        problems = self.run_check({"X/Exports/D.lean": NO_READER})
        self.assertEqual(len(problems), 1)
        self.assertIn("export dExport takes a fork but never caps it", problems[0])

    def test_readers_and_proofs_are_skipped(self):
        files = {"Base/Exports.lean": UNCAPPED, "X/Proofs/C.lean": UNCAPPED}
        self.assertEqual(self.run_check(files), [])

    def test_repository_passes(self):
        self.assertEqual(cap.check(HERE.parent), [])


if __name__ == "__main__":
    unittest.main()
