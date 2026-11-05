"""The release archives of `tests/sources.toml`, in the cache that `ETHLIB_ARCHIVES` names."""

import importlib.util
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]

# The fetcher, loaded by path: `scripts` is not a package.
_spec = importlib.util.spec_from_file_location(
    "fetch_archives", REPO / "scripts" / "fetch_archives.py"
)
fetch_archives = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(fetch_archives)

# The cache, or `None` when the archives are not to be read.
CACHE = fetch_archives.cache_from_environment()


def unpack(name: str, *paths: str) -> Path:
    """The directory of the archive `name`, with every member under `paths` unpacked."""
    return fetch_archives.unpack(fetch_archives.load(REPO)[name], CACHE, list(paths))
