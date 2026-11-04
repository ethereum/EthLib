"""The marker `archive`, for a test that reads a release archive."""

from pathlib import Path

import pytest

import archives


def pytest_collection_modifyitems(items) -> None:
    """Skip every test marked `archive` when `ETHLIB_ARCHIVES` is unset."""
    if archives.CACHE is not None:
        return
    skip = pytest.mark.skip(
        reason=f"set {archives.fetch_archives.ENVIRONMENT} to a cache directory to read the "
               "release archives")
    for item in items:
        if item.get_closest_marker("archive") is not None:
            item.add_marker(skip)


@pytest.fixture
def archive(request) -> Path:
    """The directory of the archive that the test's marker names, with its paths unpacked."""
    marker = request.node.get_closest_marker("archive")
    return archives.unpack(*marker.args)
