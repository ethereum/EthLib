"""The chain configuration that the exports read as JSON."""

import pytest

from ethlib import engine
from raising import raises

# Paris from block 0, the smallest configuration that the payload checks run on.
ACTIVATIONS = [["paris", "block", 0]]

# The message when the configuration parses and the request then has no parameter.
NO_PARAMS = 'engine error: EthLib.Engine.EngineError.invalidParams "params: not 1 values"'


def test_chain_id_above_64_bits() -> None:
    """A chain ID of 2^64 does not fit the 64-bit type, so the configuration is rejected."""
    config = {"chainId": 2**64, "depositContractAddress": bytes(20), "activations": ACTIVATIONS}
    with raises(engine.EngineError, "config: chainId is not below 2^64") as error:
        engine.new_payload(config, "engine_newPayloadV1", [])
    assert error.value.code == 0


def test_largest_chain_id() -> None:
    """A chain ID of 2^64 - 1 is accepted, and the request is checked next."""
    config = {"chainId": 2**64 - 1, "depositContractAddress": bytes(20), "activations": ACTIVATIONS}
    with raises(engine.EngineError, NO_PARAMS) as error:
        engine.new_payload(config, "engine_newPayloadV1", [])
    assert error.value.code == 32602


def test_deposit_contract_missing() -> None:
    """A configuration without a deposit contract address is rejected, since no default fits."""
    config = {"chainId": 1, "activations": ACTIVATIONS}
    with raises(engine.EngineError, "config: no depositContractAddress") as error:
        engine.new_payload(config, "engine_newPayloadV1", [])
    assert error.value.code == 0


@pytest.mark.parametrize(
    ("address", "fault"),
    [
        (1, "is not text"),
        ("00000000219ab540356cbb839cbe05303d7705fa", "does not start with 0x"),
        ("0x00000000219ab540356cbb839cbe05303d7705fg", "is not hex"),
        ("0x00000000219ab540356cbb839cbe05303d7705f", "is not forty hex digits"),
        (bytes(19), "is not forty hex digits"),
        (bytes(21), "is not forty hex digits"),
    ],
    ids=["number", "no-0x", "not-hex", "39-digits", "19-bytes", "21-bytes"],
)
def test_deposit_contract_malformed(address: int | str | bytes, fault: str) -> None:
    """An address that is not text, has no 0x, a digit that is not hex or not forty is rejected."""
    config = {"chainId": 1, "depositContractAddress": address, "activations": ACTIVATIONS}
    with raises(engine.EngineError, f"config: depositContractAddress {fault}") as error:
        engine.new_payload(config, "engine_newPayloadV1", [])
    assert error.value.code == 0


def test_deposit_contract_mixed_case() -> None:
    """Hex digits are read in either case, as a genesis file gives a checksummed address."""
    address = "0x00000000219ab540356cBB839Cbe05303d7705Fa"
    config = {"chainId": 1, "depositContractAddress": address, "activations": ACTIVATIONS}
    with raises(engine.EngineError, NO_PARAMS) as error:
        engine.new_payload(config, "engine_newPayloadV1", [])
    assert error.value.code == 32602
