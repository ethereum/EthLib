"""Tests of the release version check and the release manifest."""

import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import release_manifest  # noqa: E402

LAKEFILE = 'package «EthLib» where\n  version := v!"{}"\n'
PYPROJECT = '[project]\nname = "ethlib"\nversion = "{}"\n'
LAKE_MANIFEST = {
    "version": "1.3.0",
    "packages": [
        {"name": "mathlib", "url": "https://example.org/mathlib", "rev": "abc"},
        {"name": "VCVio", "url": "https://example.org/vcvio", "rev": "def"},
    ],
}
SOURCES = '[repositories."ethereum/EIPs"]\ncommit = "0123"\n'
EXPORTS = "@[export eth_b]\ndef b := 1\n@[export eth_a]\ndef a := 2\n"


class ReleaseManifestTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        (self.root / "EthLib" / "Exports").mkdir(parents=True)
        (self.root / "tests").mkdir()
        (self.root / "EthLib" / "Exports" / "Some.lean").write_text(EXPORTS)
        (self.root / "tests" / "sources.toml").write_text(SOURCES)
        (self.root / "lake-manifest.json").write_text(json.dumps(LAKE_MANIFEST))
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
        self.write_versions("1.2.3", "1.2.3")

    def tearDown(self):
        self.tmp.cleanup()

    def write_versions(self, python, lake):
        (self.root / "pyproject.toml").write_text(PYPROJECT.format(python))
        (self.root / "lakefile.lean").write_text(LAKEFILE.format(lake))

    def test_agreeing_versions_pass(self):
        self.assertEqual(release_manifest.version_errors(self.root, "v1.2.3"), [])

    def test_different_versions_fail(self):
        self.write_versions("1.2.3", "1.2.4")
        self.assertEqual(len(release_manifest.version_errors(self.root, None)), 1)

    def test_wrong_tag_fails(self):
        self.assertEqual(len(release_manifest.version_errors(self.root, "v1.2.4")), 1)

    def test_version_must_have_three_numbers(self):
        self.write_versions("1.2", "1.2")
        self.assertEqual(len(release_manifest.version_errors(self.root, None)), 1)

    def test_missing_lake_version_fails(self):
        (self.root / "lakefile.lean").write_text("package «EthLib» where\n")
        self.assertEqual(len(release_manifest.version_errors(self.root, None)), 1)

    def test_manifest(self):
        m = release_manifest.manifest(self.root)
        self.assertEqual(m["version"], "1.2.3")
        self.assertEqual(m["lean_toolchain"], "leanprover/lean4:v4.35.0")
        self.assertEqual([p["name"] for p in m["packages"]], ["VCVio", "mathlib"])
        self.assertEqual(m["fixture_sources"]["repositories"]["ethereum/EIPs"]["commit"], "0123")
        self.assertEqual(m["exports"], ["eth_a", "eth_b"])

    def test_main_writes_the_manifest(self):
        out = self.root / "manifest.json"
        code = release_manifest.main(["--root", str(self.root), "--check", "--output", str(out)])
        self.assertEqual(code, 0)
        self.assertEqual(json.loads(out.read_text())["version"], "1.2.3")

    def test_main_fails_on_a_wrong_tag(self):
        code = release_manifest.main(["--root", str(self.root), "--check", "--tag", "v9.9.9"])
        self.assertEqual(code, 1)

    def test_repository_versions_agree(self):
        self.assertEqual(release_manifest.version_errors(release_manifest.ROOT, None), [])


if __name__ == "__main__":
    unittest.main()
