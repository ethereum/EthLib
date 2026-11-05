"""
Check the pinned test vectors.

The BLS, KZG, secp256k1 and secp256r1 vectors are pinned: each directory must hold a `SHA256SUMS`
file, and a missing one is an error, so deleting it cannot switch the check
off. Any other vector directory that holds a `SHA256SUMS` file is pinned too.
Every `data.yaml` under a pinned directory must be listed there, with the
listed digest.
Regenerating a vector that changes its answer then fails this check.

With `--upstream`, also check that the pinned digests are the ones
upstream published, in the archives that `tests/sources.toml` pins.
The archives are downloaded into the cache of scripts/fetch_archives.py.
consensus-specs published most of the digests, in the general test archive of its last release
before the KZG specification moved here (consensus-specs#5398). That archive has no BLS signing
or verification cases, so those come from the ethereum/bls12-381-tests release archive.

    uv run --no-project --python 3.12 python tests/cryptography/check_vectors.py
    uv run --no-project --python 3.12 python tests/cryptography/check_vectors.py --upstream
    uv run --no-project --python 3.12 python tests/cryptography/check_vectors.py --upstream \
        --archive general.tar.gz --bls-archive bls_tests_yaml.tar.gz

Only the standard library is used, so the check needs no Lean and no
install step.
"""

import argparse
import hashlib
import importlib.util
import sys
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent

# The suites that must be pinned. Their manifests are checked in CI.
REQUIRED = ("bls", "kzg", "secp256k1", "secp256r1")

# The fetcher of the release archives that `tests/sources.toml` pins, loaded by path:
# `scripts` is not a package.
_spec = importlib.util.spec_from_file_location(
    "fetch_archives", ROOT.parents[1] / "scripts" / "fetch_archives.py"
)
fetch_archives = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(fetch_archives)

# The general test archive of consensus-specs v1.7.0-alpha.12, the last release before
# consensus-specs#5398.
# The cases come from this archive.
# The pins in tests/sources.toml hold the same bytes.
UPSTREAM = "consensus-specs/v1.7.0-alpha.12/general"

# The release archive of ethereum/bls12-381-tests v0.1.2.
BLS_TESTS = "bls12-381-tests/v0.1.2/bls_tests_yaml"

# The handlers of that archive that are pinned here, under `bls/`.
BLS_TESTS_HANDLERS = (
    "aggregate",
    "aggregate_verify",
    "deserialization_G1",
    "deserialization_G2",
    "fast_aggregate_verify",
    "hash_to_G2",
    "sign",
    "verify",
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    """The digest of a file, read in chunks: the upstream archive is about 170 MB."""
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def read_sums(path: Path) -> dict[str, str]:
    """The `SHA256SUMS` file at `path`, as a map from relative path to digest.

    A line that starts with `#` names a source, and `sha256sum -c` skips it too."""
    sums = {}
    for line in path.read_text().splitlines():
        if line.startswith("#"):
            continue
        digest, name = line.split(maxsplit=1)
        sums[name] = digest
    return sums


def pinned_dirs(root: Path) -> list[Path]:
    """The required suites, and any other directory with a manifest."""
    found = {p.parent.name for p in root.glob("*/SHA256SUMS")}
    return [root / name for name in sorted(found | set(REQUIRED))]


def check_local(root: Path = ROOT) -> list[str]:
    """Every pinned directory has a manifest, which lists every vector in it with its digest."""
    errors = []
    for d in pinned_dirs(root):
        if not (d / "SHA256SUMS").is_file():
            errors.append(f"{d.name}/SHA256SUMS: missing, so nothing in {d.name} is checked")
            continue
        sums = read_sums(d / "SHA256SUMS")
        on_disk = {p.relative_to(d).as_posix() for p in d.rglob("data.yaml")}
        for name in sorted(on_disk - sums.keys()):
            errors.append(f"{d.name}/{name}: not listed in SHA256SUMS")
        for name, digest in sorted(sums.items()):
            path = d / name
            if not path.is_file():
                errors.append(f"{d.name}/{name}: listed but missing")
            elif sha256(path.read_bytes()) != digest:
                errors.append(f"{d.name}/{name}: digest differs from SHA256SUMS")
    return errors


def upstream_digests(archive: Path) -> dict[tuple[str, str], str]:
    """Digests of the upstream vectors, keyed by pinned directory and relative path.

    Upstream lays a case out as

        tests/general/<fork>/<kind>/<handler>/<suite>/<case>/data.yaml

    and this repository as `<kind>/<handler>/<case>/data.yaml`.
    The archive is read in place: no member is extracted to disk.
    """
    digests = {}
    with tarfile.open(archive, "r:gz") as tar:
        for member in tar:
            parts = member.name.split("/")
            if not member.isfile() or len(parts) != 8 or parts[:2] != ["tests", "general"]:
                continue
            _, _, _fork, kind, handler, _suite, case, leaf = parts
            if leaf != "data.yaml":
                continue
            data = tar.extractfile(member).read()
            digests[(kind, f"{handler}/{case}/data.yaml")] = sha256(data)
    return digests


def bls_tests_digests(archive: Path) -> dict[tuple[str, str], str]:
    """Digests of the pinned bls12-381-tests cases, keyed as `upstream_digests` keys them.

    That archive lays a case out as `./<handler>/<case>.yaml`, and this
    repository as `bls/<handler>/<case>/data.yaml`.
    """
    digests = {}
    with tarfile.open(archive, "r:gz") as tar:
        for member in tar:
            parts = member.name.split("/")
            if not member.isfile() or len(parts) != 3 or parts[1] not in BLS_TESTS_HANDLERS:
                continue
            _, handler, leaf = parts
            if not leaf.endswith(".yaml"):
                continue
            data = tar.extractfile(member).read()
            digests[("bls", f"{handler}/{leaf[: -len('.yaml')]}/data.yaml")] = sha256(data)
    return digests


def check_upstream(archive: Path, bls_archive: Path, root: Path = ROOT) -> tuple[list[str], int]:
    """Every upstream case is pinned here, with the upstream digest.

    A case that exists in no upstream archive is allowed, and counted.
    Returns the errors and the number of such cases.
    """
    archives = fetch_archives.load()
    if sha256_file(archive) != archives[UPSTREAM].sha256:
        return [f"{archive}: not the pinned upstream archive"], 0
    if sha256_file(bls_archive) != archives[BLS_TESTS].sha256:
        return [f"{bls_archive}: not the pinned bls12-381-tests archive"], 0
    upstream = upstream_digests(archive) | bls_tests_digests(bls_archive)
    errors, own = [], 0
    # A missing manifest is reported by `check_local`, which always runs.
    for d in pinned_dirs(root):
        if not (d / "SHA256SUMS").is_file():
            continue
        sums = read_sums(d / "SHA256SUMS")
        theirs = {name: digest for (kind, name), digest in upstream.items() if kind == d.name}
        own += len(sums.keys() - theirs.keys())
        for name in sorted(theirs.keys() - sums.keys()):
            errors.append(f"{d.name}/{name}: upstream case not pinned here")
        for name in sorted(sums.keys() & theirs.keys()):
            if sums[name] != theirs[name]:
                errors.append(f"{d.name}/{name}: digest differs from upstream")
    return errors, own


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0].strip())
    parser.add_argument(
        "--upstream",
        action="store_true",
        help="also compare the pinned digests with the upstream archive",
    )
    parser.add_argument(
        "--archive", type=Path, help="a local copy of the consensus-specs archive, not downloaded"
    )
    parser.add_argument(
        "--bls-archive",
        type=Path,
        help="a local copy of the bls12-381-tests archive, not downloaded",
    )
    args = parser.parse_args()

    errors, own = check_local(), 0
    if args.upstream:
        archives = fetch_archives.load()
        cache = fetch_archives.default_cache()
        archive = args.archive or fetch_archives.download(archives[UPSTREAM], cache)
        bls_archive = args.bls_archive or fetch_archives.download(archives[BLS_TESTS], cache)
        upstream_errors, own = check_upstream(archive, bls_archive)
        errors += upstream_errors

    for error in errors:
        print(error, file=sys.stderr)
    count = sum(
        len(read_sums(d / "SHA256SUMS")) for d in pinned_dirs(ROOT) if (d / "SHA256SUMS").is_file()
    )
    if errors:
        print(f"{len(errors)} problem(s) in {count} pinned vectors", file=sys.stderr)
        return 1
    print(f"{count} pinned vectors match their digests")
    if args.upstream:
        print(f"upstream: {count - own} match, {own} in no upstream archive")
    return 0


if __name__ == "__main__":
    sys.exit(main())
