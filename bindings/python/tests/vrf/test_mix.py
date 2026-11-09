"""Test-vector generator: `mix`, an output mixed with randomness."""

from dumper import hex_str, write_case
from ethlib.cryptography import keccak, vrf
from raising import raises

from . import fixtures


def test_mix() -> None:
    assert vrf.mix(fixtures.OUTPUT_ZERO, fixtures.RANDOMNESS) == fixtures.MIX_ZERO
    write_case(
        "vrf",
        "mix",
        "mix_zero",
        {
            "input": {
                "output": hex_str(fixtures.OUTPUT_ZERO),
                "randomness": hex_str(fixtures.RANDOMNESS),
            },
            "output": hex_str(fixtures.MIX_ZERO),
        },
    )


def test_mix_hashes_prefix_output_randomness() -> None:
    # The mix hashes the prefix, the output, then the randomness.
    for output, randomness in [
        (fixtures.OUTPUT_ZERO, fixtures.RANDOMNESS),
        (fixtures.RANDOMNESS, fixtures.OUTPUT_ZERO),
        (bytes(32), bytes(32)),
    ]:
        expected = keccak.keccak256(b"PQ_VRF_MIX" + output + randomness)
        assert vrf.mix(output, randomness) == expected


def test_rejects_bad_arguments() -> None:
    # The output and the randomness are exactly 32 bytes.
    with raises(ValueError, "output: expected 32 bytes, got 31"):
        vrf.mix(fixtures.OUTPUT_ZERO[:31], fixtures.RANDOMNESS)
    with raises(ValueError, "randomness: expected 32 bytes, got 33"):
        vrf.mix(fixtures.OUTPUT_ZERO, fixtures.RANDOMNESS + b"\x00")
