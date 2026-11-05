"""
Check `fetch_archives.py` itself, on small archives built in a temporary directory.

    uv run --no-project --python 3.12 python -m unittest scripts/test_fetch_archives.py

Only the standard library is used, like the script.
"""

import hashlib
import importlib.util
import io
import tarfile
import tempfile
import unittest
import zipfile
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Load the script by path: `scripts` is not a package.
spec = importlib.util.spec_from_file_location("fetch_archives", HERE / "fetch_archives.py")
assert spec and spec.loader
fetch = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fetch)

MEMBERS = {
    "./fixtures/a/one.json": b"one",
    "./fixtures/a/two.json": b"two",
    "./fixtures/b/three.json": b"three",
}


def tar_gz(members: dict[str, bytes], links: dict[str, str] | None = None) -> bytes:
    """A gzip-compressed tar file with the regular files `members` and the symbolic `links`."""
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode="w:gz") as tar:
        for name, data in members.items():
            info = tarfile.TarInfo(name)
            info.size = len(data)
            tar.addfile(info, io.BytesIO(data))
        for name, target in (links or {}).items():
            info = tarfile.TarInfo(name)
            info.type = tarfile.SYMTYPE
            info.linkname = target
            tar.addfile(info)
    return buffer.getvalue()


def zip_file(members: dict[str, bytes], links: dict[str, str] | None = None) -> bytes:
    """A zip file with the regular files `members` and the symbolic `links`."""
    buffer = io.BytesIO()
    with zipfile.ZipFile(buffer, "w") as zipped:
        for name, data in members.items():
            zipped.writestr(name, data)
        for name, target in (links or {}).items():
            info = zipfile.ZipInfo(name)
            info.external_attr = 0o120777 << 16
            zipped.writestr(info, target)
    return buffer.getvalue()


class Fetch(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.cache = self.root / "cache"

    def tearDown(self):
        self.tmp.cleanup()

    def archive(
        self, data: bytes, sha256: str | None = None, name: str = "served.tar.gz"
    ) -> "fetch.Archive":
        """An archive served from a local file, pinned to `sha256` or else to its own digest."""
        path = self.root / name
        path.write_bytes(data)
        digest = sha256 or hashlib.sha256(data).hexdigest()
        return fetch.Archive("vectors", path.as_uri(), len(data), digest)

    def test_download_checks_the_digest(self):
        data = tar_gz(MEMBERS)
        path = fetch.download(self.archive(data), self.cache)
        self.assertEqual(path.read_bytes(), data)

    def test_download_of_another_file_fails(self):
        with self.assertRaises(fetch.ArchiveError):
            fetch.download(self.archive(tar_gz(MEMBERS), "0" * 64), self.cache)
        self.assertEqual(list(self.cache.glob("*.gz")) + list(self.cache.glob("*.part")), [])

    def test_cached_copy_is_not_downloaded_again(self):
        archive = self.archive(tar_gz(MEMBERS))
        fetch.download(archive, self.cache)
        (self.root / "served.tar.gz").unlink()
        self.assertTrue(fetch.download(archive, self.cache).is_file())

    def test_unpack_only_the_paths_asked(self):
        archive = self.archive(tar_gz(MEMBERS))
        target = fetch.unpack(archive, self.cache, ["fixtures/a"])
        self.assertEqual((target / "fixtures/a/two.json").read_bytes(), b"two")
        self.assertFalse((target / "fixtures/b").exists())
        target = fetch.unpack(archive, self.cache, ["fixtures/b/three.json"])
        self.assertEqual((target / "fixtures/b/three.json").read_bytes(), b"three")

    def test_unpacked_paths_are_not_read_again(self):
        archive = self.archive(tar_gz(MEMBERS))
        fetch.unpack(archive, self.cache, ["fixtures"])
        (self.cache / f"{archive.sha256}.tar.gz").unlink()
        (self.root / "served.tar.gz").unlink()
        self.assertTrue(fetch.unpack(archive, self.cache, ["fixtures/a"]).is_dir())

    def test_members_are_listed_once(self):
        archive = self.archive(tar_gz(MEMBERS, {"fixtures/a/link": "one.json"}))
        expected = ["fixtures/a/one.json", "fixtures/a/two.json", "fixtures/b/three.json"]
        self.assertEqual(fetch.members(archive, self.cache), expected)
        (self.cache / f"{archive.sha256}.tar.gz").unlink()
        (self.root / "served.tar.gz").unlink()
        self.assertEqual(fetch.members(archive, self.cache), expected)

    def test_path_without_member_fails(self):
        with self.assertRaisesRegex(fetch.ArchiveError, "no member under fixtures/c"):
            fetch.unpack(self.archive(tar_gz(MEMBERS)), self.cache, ["fixtures/c"])

    def test_path_outside_the_archive_fails(self):
        for path in ("../fixtures", "/fixtures", "", "."):
            with self.subTest(path=path), self.assertRaises(fetch.ArchiveError):
                fetch.unpack(self.archive(tar_gz(MEMBERS)), self.cache, [path])

    def test_member_that_leaves_the_directory_fails(self):
        archive = self.archive(tar_gz({"fixtures/../../escape": b"x"}))
        with self.assertRaisesRegex(fetch.ArchiveError, "unsafe member"):
            fetch.unpack(archive, self.cache, ["fixtures"])
        self.assertFalse((self.root / "escape").exists())

    def test_link_fails(self):
        archive = self.archive(tar_gz(MEMBERS, {"fixtures/a/link": "/etc/passwd"}))
        with self.assertRaisesRegex(fetch.ArchiveError, "not a file or a directory"):
            fetch.unpack(archive, self.cache, ["fixtures/a"])

    def test_zip(self):
        archive = self.archive(zip_file(MEMBERS), name="served.zip")
        expected = ["fixtures/a/one.json", "fixtures/a/two.json", "fixtures/b/three.json"]
        self.assertEqual(fetch.members(archive, self.cache), expected)
        target = fetch.unpack(archive, self.cache, ["fixtures/a"])
        self.assertEqual((target / "fixtures/a/two.json").read_bytes(), b"two")
        self.assertFalse((target / "fixtures/b").exists())
        self.assertTrue((self.cache / f"{archive.sha256}.zip").is_file())

    def test_zip_member_that_leaves_the_directory_fails(self):
        archive = self.archive(zip_file({"fixtures/../../escape": b"x"}), name="served.zip")
        with self.assertRaisesRegex(fetch.ArchiveError, "unsafe member"):
            fetch.unpack(archive, self.cache, ["fixtures"])
        self.assertFalse((self.root / "escape").exists())

    def test_zip_link_fails(self):
        archive = self.archive(
            zip_file(MEMBERS, {"fixtures/a/link": "/etc/passwd"}), name="served.zip"
        )
        with self.assertRaisesRegex(fetch.ArchiveError, "not a file or a directory"):
            fetch.unpack(archive, self.cache, ["fixtures/a"])


if __name__ == "__main__":
    unittest.main()
