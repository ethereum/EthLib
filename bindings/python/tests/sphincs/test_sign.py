"""Test-vector generator: `sign`."""

from dumper import hex_str, write_case
from ethlib.cryptography import sphincs

from . import fixtures

HANDLER = "sign"


def _emit(case: str, seed: bytes, message: bytes) -> None:
    # Inputs of the wrong length are rejected, written as a null output.
    try:
        result = hex_str(sphincs.sign(seed, message))
    except (ValueError, RuntimeError):
        result = None
    write_case(
        "sphincs",
        HANDLER,
        case,
        {
            "input": {
                "seed": hex_str(seed),
                "message": hex_str(message),
            },
            "output": result,
        },
    )


@fixtures.slow
def test_known_answer() -> None:
    _emit(f"{HANDLER}_known_answer", fixtures.SEED_KNOWN_ANSWER, fixtures.MESSAGE_KNOWN_ANSWER)


@fixtures.slow
def test_zero_message() -> None:
    # Another message under the same key: another FORS instance and other leaves.
    _emit(f"{HANDLER}_zero_message", fixtures.SEED_KNOWN_ANSWER, fixtures.MESSAGE_ZERO)


@fixtures.slow
def test_zero_seed() -> None:
    # The same message under another key.
    _emit(f"{HANDLER}_zero_seed", fixtures.SEED_ZERO, fixtures.MESSAGE_KNOWN_ANSWER)


def test_short_message() -> None:
    # 31 bytes: rejected before any tree is built.
    _emit(
        f"{HANDLER}_short_message", fixtures.SEED_KNOWN_ANSWER, fixtures.MESSAGE_KNOWN_ANSWER[:-1]
    )


def test_short_seed() -> None:
    _emit(f"{HANDLER}_short_seed", fixtures.SEED_KNOWN_ANSWER[:-1], fixtures.MESSAGE_KNOWN_ANSWER)
