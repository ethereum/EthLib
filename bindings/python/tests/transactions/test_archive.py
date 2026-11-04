"""The vendored transaction tests against the release archive of execution-specs."""

from pathlib import Path

import pytest

ARCHIVE = "execution-specs/tests@v21.0.2/fixtures"
MEMBERS = "fixtures/transaction_tests"

_REPO = Path(__file__).resolve().parents[4]
_FIXTURES = _REPO / "tests" / "execution" / "transactions"
VENDORED = sorted(p.relative_to(_FIXTURES).as_posix() for p in _FIXTURES.rglob("*.json"))

pytestmark = pytest.mark.archive(ARCHIVE, MEMBERS)


@pytest.mark.parametrize("path", VENDORED)
def test_copy(archive, path) -> None:
    # The vendored file is the file of the release, byte for byte.
    assert (_FIXTURES / path).read_bytes() == (archive / MEMBERS / path).read_bytes()


def test_every_fork_in_scope(archive) -> None:
    released = sorted(p.relative_to(archive / MEMBERS).as_posix()
                      for p in (archive / MEMBERS).rglob("*.json"))
    assert VENDORED == released
