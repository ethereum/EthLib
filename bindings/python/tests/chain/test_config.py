"""The chain configuration that the exports read as JSON."""

from ethlib import engine
from raising import raises

# Paris from block 0, the smallest configuration that the payload checks run on.
ACTIVATIONS = [["paris", "block", 0]]


def test_chain_id_above_64_bits() -> None:
    """A chain ID of 2^64 does not fit the 64-bit type, so the configuration is rejected."""
    config = {"chainId": 2**64, "activations": ACTIVATIONS}
    with raises(engine.EngineError, "config: chainId is not below 2^64") as error:
        engine.new_payload(config, "engine_newPayloadV1", [])
    assert error.value.code == 0


def test_largest_chain_id() -> None:
    """A chain ID of 2^64 - 1 is accepted, and the request is checked next."""
    config = {"chainId": 2**64 - 1, "activations": ACTIVATIONS}
    with raises(
        engine.EngineError,
        'engine error: EthLib.Engine.EngineError.invalidParams "params: not 1 values"',
    ) as error:
        engine.new_payload(config, "engine_newPayloadV1", [])
    assert error.value.code == 32602
