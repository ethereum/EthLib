"""The answer of engine_getInclusionListV1, from the candidates of a node."""

from typing import Any

import pytest

from ethlib import engine
from raising import raises

# The most bytes that the transactions of an inclusion list hold together, from bogota.md.
MAX_BYTES = 2**13
METHOD = "engine_getInclusionListV1"


def test_empty_and_overflowing_candidates_are_dropped() -> None:
    """Candidates of 5000, 0, 4000 and 3000 bytes give those of 5000 and 3000 bytes."""
    candidates = [b"\x01" * 5000, b"", b"\x02" * 4000, b"\x03" * 3000]
    answer = engine.get_inclusion_list(candidates, METHOD, [])
    assert answer == ["0x" + "01" * 5000, "0x" + "03" * 3000]


def test_list_that_fits_is_kept() -> None:
    """Candidates that keep both rules come back whole, in order, up to exactly the bound."""
    candidates = [b"\x00", b"\x02\xf8", b"\x04" * (MAX_BYTES - 3)]
    answer = engine.get_inclusion_list(candidates, METHOD, [])
    assert answer == ["0x" + c.hex() for c in candidates]


def test_one_byte_past_the_bound() -> None:
    """A candidate that would take the list one byte past the bound is dropped."""
    candidates = [b"\x05" * MAX_BYTES, b"\x06"]
    assert engine.get_inclusion_list(candidates, METHOD, []) == ["0x" + "05" * MAX_BYTES]


@pytest.mark.parametrize(
    ("params", "reason"),
    [
        pytest.param([1], "params: got 1, expected 0", id="one-value"),
        pytest.param({}, "params: not an array", id="object"),
    ],
)
def test_parameters(params: Any, reason: str) -> None:
    """The method takes no parameter, so anything but an empty array is an invalid parameter."""
    message = f'engine error: EthLib.Engine.EngineError.invalidParams "{reason}"'
    with raises(engine.EngineError, message) as error:
        engine.get_inclusion_list([], METHOD, params)
    assert error.value.code == 32602


def test_other_method() -> None:
    """A request for another method has code 0."""
    with raises(engine.EngineError, "no method engine_getInclusionListV2") as error:
        engine.get_inclusion_list([], "engine_getInclusionListV2", [])
    assert error.value.code == 0
