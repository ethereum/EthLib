"""
Download the release archives of `tests/sources.toml` into a cache, and unpack parts of them.

    uv run --no-project --python 3.12 python scripts/fetch_archives.py --list
    uv run --no-project --python 3.12 python scripts/fetch_archives.py --cache DIR NAME \
        [--path PATH ...]

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
def locked(cache: Path):
    """Hold the lock of the cache, so that two processes do not write one file together."""
    cache.mkdir(parents=True, exist_ok=True)
    with (cache / ".lock").open("w") as lock:
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


def _download(archive: Archive, cache: Path) -> Path:
    """The file `<sha256>.tar.gz` of the cache, checked against the pin."""
    path = cache / f"{archive.sha256}.tar.gz"
    if path.is_file() and path.stat().st_size == archive.size and _digest(path) == archive.sha256:
        return path
    part = path.with_suffix(".part")
    h, size = hashlib.sha256(), 0
    with urllib.request.urlopen(archive.url) as response, part.open("wb") as out:
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
    with locked(cache):
        return _download(archive, cache)


def _member_path(name: str) -> PurePosixPath | None:
    """The path of a member, without a leading `./`, or `None` if it would leave the directory."""
    path = PurePosixPath(name)
    if path.is_absolute() or ".." in path.parts:
        return None
    return PurePosixPath(*[part for part in path.parts if part != "."])


def _under(path: PurePosixPath, prefixes: list[PurePosixPath]) -> bool:
    return any(path == prefix or prefix in path.parents for prefix in prefixes)


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
    with locked(cache):
        record = target / UNPACKED
        done = set(json.loads(record.read_text())) if record.is_file() else set()
        missing = [p for p in prefixes if not _under(p, [PurePosixPath(d) for d in done])]
        if not missing:
            return target
        source = _download(archive, cache)
        matched = set()
        with tarfile.open(source, "r:*") as tar:
            for member in tar:
                path = _member_path(member.name)
                if path is None:
                    if _under(PurePosixPath(member.name), missing):
                        raise ArchiveError(f"{archive.name}: unsafe member {member.name}")
                    continue
                if not _under(path, missing):
                    continue
                matched.update(p for p in missing if _under(path, [p]))
                if member.isdir():
                    (target / path).mkdir(parents=True, exist_ok=True)
                elif member.isfile():
                    (target / path).parent.mkdir(parents=True, exist_ok=True)
                    with tar.extractfile(member) as data, (target / path).open("wb") as out:
                        shutil.copyfileobj(data, out, CHUNK)
                else:
                    raise ArchiveError(f"{archive.name}: {member.name} is not a file or a "
                                       f"directory")
        if unmatched := sorted(p.as_posix() for p in set(missing) - matched):
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
