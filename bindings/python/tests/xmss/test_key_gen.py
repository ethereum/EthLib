"""Test-vector generator: `key_gen`."""

from dumper import hex_str, write_case
from ethlib.cryptography import xmss

from . import fixtures

HANDLER = "key_gen"


def _emit(case: str, seed: bytes) -> None:
    # A seed of any other length is rejected, written as a null output.
    try:
        result = hex_str(xmss.key_gen(seed))
    except (ValueError, RuntimeError):
        result = None
    write_case(
        "xmss",
        HANDLER,
        case,
        {
            "input": {"seed": hex_str(seed)},
            "output": result,
        },
    )


@fixtures.slow
def test_known_answer() -> None:
    _emit(f"{HANDLER}_known_answer", fixtures.SEED_KNOWN_ANSWER)


@fixtures.slow
def test_zero_seed() -> None:
    _emit(f"{HANDLER}_zero_seed", fixtures.SEED_ZERO)


def test_short_seed() -> None:
    # One byte short: rejected before any hashing.
    _emit(f"{HANDLER}_short_seed", fixtures.SEED_KNOWN_ANSWER[:-1])


def test_long_seed() -> None:
    # 33 bytes: rejected, never truncated.
    _emit(f"{HANDLER}_long_seed", fixtures.SEED_KNOWN_ANSWER + b"\x00")
