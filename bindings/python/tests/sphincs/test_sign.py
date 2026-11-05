"""Test-vector generator: `sign`."""

from dumper import hex_str, write_case
from ethlib.cryptography import sphincs

from . import fixtures as F

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


@F.slow
def test_known_answer() -> None:
    _emit(f"{HANDLER}_known_answer", F.SEED_KNOWN_ANSWER, F.MESSAGE_KNOWN_ANSWER)


@F.slow
def test_zero_message() -> None:
    # Another message under the same key: another FORS instance and other leaves.
    _emit(f"{HANDLER}_zero_message", F.SEED_KNOWN_ANSWER, F.MESSAGE_ZERO)


@F.slow
def test_zero_seed() -> None:
    # The same message under another key.
    _emit(f"{HANDLER}_zero_seed", F.SEED_ZERO, F.MESSAGE_KNOWN_ANSWER)


def test_short_message() -> None:
    # 31 bytes: rejected before any tree is built.
    _emit(f"{HANDLER}_short_message", F.SEED_KNOWN_ANSWER, F.MESSAGE_KNOWN_ANSWER[:31])


def test_short_seed() -> None:
    _emit(f"{HANDLER}_short_seed", F.SEED_KNOWN_ANSWER[:31], F.MESSAGE_KNOWN_ANSWER)
