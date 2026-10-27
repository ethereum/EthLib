"""
Check `check_vectors.py` itself, on a small vector tree built in a temporary
directory.

    python3 -m unittest tests/cryptography/test_check_vectors.py

Only the standard library is used, like the check.
"""
import hashlib
import importlib.util
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Load the check by path: `tests/cryptography` is not a package.
spec = importlib.util.spec_from_file_location("check_vectors", HERE / "check_vectors.py")
check_vectors = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check_vectors)


def write_suite(root: Path, name: str, cases: dict[str, bytes]) -> None:
    """One suite: its `data.yaml` files, and a manifest that lists them all."""
    lines = []
    for case, data in cases.items():
        path = root / name / case / "data.yaml"
        path.parent.mkdir(parents=True)
        path.write_bytes(data)
        lines.append(f"{hashlib.sha256(data).hexdigest()}  {case}/data.yaml")
    (root / name / "SHA256SUMS").write_text("\n".join(lines) + "\n")


class CheckLocal(unittest.TestCase):

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        write_suite(self.root, "bls", {"sign/case_0": b"bls 0"})
        write_suite(self.root, "kzg", {"blob/case_0": b"kzg 0", "blob/case_1": b"kzg 1"})

    def tearDown(self):
        self.tmp.cleanup()

    def errors(self) -> list[str]:
        return check_vectors.check_local(self.root)

    def test_intact_tree_passes(self):
        self.assertEqual(self.errors(), [])

    def test_missing_kzg_manifest_fails(self):
        (self.root / "kzg" / "SHA256SUMS").unlink()
        self.assertEqual(self.errors(), ["kzg/SHA256SUMS: missing, so nothing in kzg is checked"])

    def test_missing_both_manifests_fails(self):
        (self.root / "bls" / "SHA256SUMS").unlink()
        (self.root / "kzg" / "SHA256SUMS").unlink()
        self.assertEqual(len(self.errors()), 2)

    def test_missing_suite_fails(self):
        for path in sorted((self.root / "kzg").rglob("*"), reverse=True):
            path.unlink() if path.is_file() else path.rmdir()
        (self.root / "kzg").rmdir()
        self.assertEqual(self.errors(), ["kzg/SHA256SUMS: missing, so nothing in kzg is checked"])

    def test_changed_case_fails(self):
        (self.root / "kzg" / "blob" / "case_0" / "data.yaml").write_bytes(b"changed")
        self.assertEqual(self.errors(), ["kzg/blob/case_0/data.yaml: digest differs from SHA256SUMS"])

    def test_unlisted_case_fails(self):
        extra = self.root / "kzg" / "blob" / "case_2" / "data.yaml"
        extra.parent.mkdir()
        extra.write_bytes(b"kzg 2")
        self.assertEqual(self.errors(), ["kzg/blob/case_2/data.yaml: not listed in SHA256SUMS"])

    def test_deleted_case_fails(self):
        (self.root / "kzg" / "blob" / "case_1" / "data.yaml").unlink()
        self.assertEqual(self.errors(), ["kzg/blob/case_1/data.yaml: listed but missing"])

    def test_other_pinned_suite_is_checked(self):
        write_suite(self.root, "xmss", {"sign/case_0": b"xmss 0"})
        (self.root / "xmss" / "sign" / "case_0" / "data.yaml").write_bytes(b"changed")
        self.assertEqual(self.errors(), ["xmss/sign/case_0/data.yaml: digest differs from SHA256SUMS"])


if __name__ == "__main__":
    unittest.main()
