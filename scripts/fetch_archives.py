"""
Download the release archives of `tests/sources.toml` into a cache, and unpack parts of them.

    uv run --no-project --python 3.12 python scripts/fetch_archives.py --list
    uv run --no-project --python 3.12 python scripts/fetch_archives.py --cache DIR NAME \
        [--path PATH ...]

An archive is a tar file, compressed or not, or a zip file when its URL ends in `.zip`.

The cache is the directory that `ETHLIB_ARCHIVES` names.
Without it, the cache is `ethlib/archives` in the user's cache directory, such as `~/.cache`.
"""
import argparse
import contextlib
import hashlib
import json
import os
import shutil
import sys
import tarfile
import tomllib
import urllib.request
import zipfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parent.parent

SOURCES = "tests/sources.toml"
ENVIRONMENT = "ETHLIB_ARCHIVES"
CHUNK = 1 << 20
UNPACKED = ".unpacked.json"


class ArchiveError(Exception):
    """An archive that is not the pinned one, or that cannot be unpacked safely."""


@dataclass(frozen=True)
class Archive:
    """One pinned release archive."""

    name: str
    url: str
    size: int
    sha256: str


def load(root: Path = ROOT) -> dict[str, Archive]:
    """The archives that `tests/sources.toml` pins, by name."""
    config = tomllib.loads((root / SOURCES).read_text(encoding="utf-8"))
    return {name: Archive(name, entry["url"], entry["size"], entry["sha256"])
            for name, entry in config.get("archives", {}).items()}


@contextlib.contextmanager
def locked(cache: Path, archive: Archive):
    """Hold the lock of one archive in the cache, so that two processes do not write one file."""
    cache.mkdir(parents=True, exist_ok=True)
    with (cache / f"{archive.sha256}.lock").open("w") as lock:
        try:
            import fcntl
        except ImportError:
            yield
            return
        fcntl.flock(lock, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(lock, fcntl.LOCK_UN)


def _digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(CHUNK), b""):
            h.update(chunk)
    return h.hexdigest()


def _is_zip(archive: Archive) -> bool:
    return archive.url.endswith(".zip")


def _download(archive: Archive, cache: Path) -> Path:
    """The file `<sha256>.tar.gz` or `<sha256>.zip` of the cache, checked against the pin."""
    path = cache / (archive.sha256 + (".zip" if _is_zip(archive) else ".tar.gz"))
    if path.is_file() and path.stat().st_size == archive.size and _digest(path) == archive.sha256:
        return path
    part = path.with_suffix(".part")
    h, size = hashlib.sha256(), 0
    # Some hosts, such as csrc.nist.gov, refuse the default user agent of urllib.
    request = urllib.request.Request(archive.url, headers={"User-Agent": "ethlib-fetch-archives"})
    with urllib.request.urlopen(request) as response, part.open("wb") as out:
        for chunk in iter(lambda: response.read(CHUNK), b""):
            size += len(chunk)
            if size > archive.size:
                break
            h.update(chunk)
            out.write(chunk)
    if size != archive.size or h.hexdigest() != archive.sha256:
        part.unlink()
        raise ArchiveError(f"{archive.url}: not the pinned archive {archive.name} "
                           f"({archive.size} bytes, sha256 {archive.sha256})")
    part.replace(path)
    return path


def download(archive: Archive, cache: Path) -> Path:
    """The archive file in the cache, downloaded first if it is missing or differs from the pin."""
    with locked(cache, archive):
        return _download(archive, cache)


def _member_path(name: str) -> PurePosixPath | None:
    """The path of a member, without a leading `./`, or `None` if it would leave the directory."""
    path = PurePosixPath(name)
    if path.is_absolute() or ".." in path.parts:
        return None
    return PurePosixPath(*[part for part in path.parts if part != "."])


def _prefixes_of(path: PurePosixPath, prefixes: set[PurePosixPath]) -> set[PurePosixPath]:
    """The prefixes that hold `path`: the path itself, or one of its parents."""
    return {ancestor for ancestor in (path, *path.parents) if ancestor in prefixes}


# The kinds of member that an archive holds.
FILE, DIRECTORY, OTHER = "file", "directory", "other"

# The type bits of a symbolic link, in the Unix mode that a zip member may carry.
_ZIP_LINK = 0o120000


def _entries(archive: Archive, source: Path):
    """Each member of the archive file: its name, its kind, and a function that opens it."""
    if _is_zip(archive):
        with zipfile.ZipFile(source) as zipped:
            for info in zipped.infolist():
                if info.is_dir():
                    kind = DIRECTORY
                elif (info.external_attr >> 16) & 0o170000 == _ZIP_LINK:
                    kind = OTHER
                else:
                    kind = FILE
                yield info.filename, kind, lambda info=info: zipped.open(info)
        return
    with tarfile.open(source, "r:*") as tar:
        for member in tar:
            kind = FILE if member.isfile() else DIRECTORY if member.isdir() else OTHER
            yield member.name, kind, lambda member=member: tar.extractfile(member)


def members(archive: Archive, cache: Path) -> list[str]:
    """The paths of the archive's regular files, listed once and then kept in the cache."""
    listing = cache / f"{archive.sha256}.members.json"
    with locked(cache, archive):
        if listing.is_file():
            return json.loads(listing.read_text())
        source = _download(archive, cache)
        paths = (_member_path(name) for name, kind, _ in _entries(archive, source) if kind == FILE)
        names = sorted(path.as_posix() for path in paths if path is not None)
        listing.write_text(json.dumps(names))
    return names


def unpack(archive: Archive, cache: Path, paths: list[str]) -> Path:
    """The directory `<sha256>/` of the cache, with every member under `paths` unpacked."""
    # A path that matches no member is an error, so a suite cannot read an empty directory.
    # The archive comes from outside the repository.
    # So only regular files and directories are written.
    # A member whose path leaves the directory is refused.
    prefixes = [_member_path(p) for p in paths]
    if not prefixes or any(p is None or not p.parts for p in prefixes):
        raise ArchiveError(f"{archive.name}: give paths inside the archive, without '..'")
    target = cache / archive.sha256
    with locked(cache, archive):
        record = target / UNPACKED
        done = set(json.loads(record.read_text())) if record.is_file() else set()
        finished = {PurePosixPath(d) for d in done}
        missing = {p for p in prefixes if not _prefixes_of(p, finished)}
        if not missing:
            return target
        source = _download(archive, cache)
        matched = set()
        for name, kind, open_member in _entries(archive, source):
            path = _member_path(name)
            if path is None:
                if _prefixes_of(PurePosixPath(name), missing):
                    raise ArchiveError(f"{archive.name}: unsafe member {name}")
                continue
            holders = _prefixes_of(path, missing)
            if not holders:
                continue
            matched |= holders
            if kind == DIRECTORY:
                (target / path).mkdir(parents=True, exist_ok=True)
            elif kind == FILE:
                (target / path).parent.mkdir(parents=True, exist_ok=True)
                with open_member() as data, (target / path).open("wb") as out:
                    shutil.copyfileobj(data, out, CHUNK)
            else:
                raise ArchiveError(f"{archive.name}: {name} is not a file or a directory")
        if unmatched := sorted(p.as_posix() for p in missing - matched):
            raise ArchiveError(f"{archive.name}: no member under {', '.join(unmatched)}")
        target.mkdir(parents=True, exist_ok=True)
        record.write_text(json.dumps(sorted(done | {p.as_posix() for p in missing}), indent=1))
    return target


def cache_from_environment() -> Path | None:
    """The cache that `ETHLIB_ARCHIVES` names, or `None` if it is unset or empty."""
    value = os.environ.get(ENVIRONMENT, "")
    return Path(value) if value else None


def default_cache() -> Path:
    """The cache that `ETHLIB_ARCHIVES` names, or else `ethlib/archives` in the user's cache."""
    xdg = os.environ.get("XDG_CACHE_HOME", "")
    user = Path(xdg) if xdg else Path.home() / ".cache"
    return cache_from_environment() or user / "ethlib" / "archives"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.strip().splitlines()[0])
    parser.add_argument("names", nargs="*", metavar="NAME", help="an archive of the table")
    parser.add_argument("--cache", type=Path, default=default_cache(),
                        help=f"the cache directory; the default is ${ENVIRONMENT}, or else "
                             "~/.cache/ethlib/archives")
    parser.add_argument("--path", action="append", default=[], dest="paths",
                        help="a file or directory to unpack, repeatable")
    parser.add_argument("--list", action="store_true", help="list the pinned archives")
    args = parser.parse_args()

    archives = load()
    if args.list:
        for archive in archives.values():
            print(f"{archive.name}  {archive.size} bytes  {archive.url}")
        return 0
    for name in args.names:
        if name not in archives:
            parser.error(f"{name} is not an archive of {SOURCES}")
    try:
        for name in args.names:
            if args.paths:
                print(unpack(archives[name], args.cache, args.paths))
            else:
                print(download(archives[name], args.cache))
    except ArchiveError as error:
        print(error, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
