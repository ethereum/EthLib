"""The marker `archive`, for a test that reads a release archive, and the parity report."""

from pathlib import Path

import pytest

import archives
from parity import report as parity

# The reason of each test marked `archive` that a run without the archives skips.
SKIP_REASON = (
    f"set {archives.fetch_archives.ENVIRONMENT} to a cache directory to read the release archives"
)


def pytest_collection_modifyitems(items) -> None:
    """Skip every test marked `archive` when `ETHLIB_ARCHIVES` is unset."""
    if archives.CACHE is not None:
        return
    skip = pytest.mark.skip(reason=SKIP_REASON)
    for item in items:
        if item.get_closest_marker("archive") is not None:
            item.add_marker(skip)


def pytest_generate_tests(metafunc) -> None:
    """Build the archive cases of a test that `archives.parametrize` marks."""
    if parameters := getattr(metafunc.function, "archive_parameters", None):
        argnames, cases = parameters
        metafunc.parametrize(argnames, cases())


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


def pytest_terminal_summary(terminalreporter) -> None:
    """Name the checks that did not run for want of the archives, so the skip is not silent."""
    # A worker under xdist sends its reports here, so the count covers every worker.
    skipped = [
        report
        for report in terminalreporter.stats.get("skipped", [])
        if isinstance(report.longrepr, tuple) and report.longrepr[2].endswith(SKIP_REASON)
    ]
    if not skipped:
        return
    # A parametrized case of a suite is one test of many, so only its function is named.
    checks = sorted({report.nodeid.split("[")[0] for report in skipped})
    terminalreporter.section("tests that did not run", sep="!", yellow=True, bold=True)
    terminalreporter.line(
        f"{len(skipped)} tests marked archive did not run: {SKIP_REASON}.", yellow=True
    )
    terminalreporter.line("The skipped tests, by function:")
    for check in checks:
        terminalreporter.line(f"  {check}")
