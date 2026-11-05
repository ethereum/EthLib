"""The marker `archive`, for a test that reads a release archive, and the parity report."""

from pathlib import Path

import pytest

import archives
from parity import report as parity


def pytest_collection_modifyitems(items) -> None:
    """Skip every test marked `archive` when `ETHLIB_ARCHIVES` is unset."""
    if archives.CACHE is not None:
        return
    skip = pytest.mark.skip(
        reason=f"set {archives.fetch_archives.ENVIRONMENT} to a cache directory to read the "
        "release archives"
    )
    for item in items:
        if item.get_closest_marker("archive") is not None:
            item.add_marker(skip)


@pytest.fixture
def archive(request) -> Path:
    """The directory of the archive that the test's marker names, with its paths unpacked."""
    marker = request.node.get_closest_marker("archive")
    return archives.unpack(*marker.args)


def pytest_runtest_logreport(report) -> None:
    """Count the outcome of a parity test."""
    parity.record(report)


def pytest_sessionfinish(session) -> None:
    """Write the parity report once, in the process that holds every outcome."""
    if not hasattr(session.config, "workerinput"):
        parity.write()
