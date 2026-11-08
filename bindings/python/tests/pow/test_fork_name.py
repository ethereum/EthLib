"""The fork of a header crosses as its name, a `str`, so bytes fail before any decoding."""

import pytest

from ethlib.errors import BlockError
from ethlib.execution.pow import check_proof_of_work, seal_hash
from raising import raises


@pytest.mark.parametrize("export", [seal_hash, check_proof_of_work])
def test_fork_name_as_bytes(export) -> None:
    with raises(BlockError, "expected a str") as error:
        export(b"london", b"")
    assert error.value.code == 0
