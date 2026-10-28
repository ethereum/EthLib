"""Test-vector generator: `sign`."""

from ethlib.cryptography import xmss

from . import fixtures as F
from dumper import hex_str, write_case


HANDLER = "sign"


def _emit(case: str, seed: bytes, leaf_index: int, message: bytes) -> None:
    # Inputs of the wrong length are rejected, written as a null output.
    try:
        result = hex_str(xmss.sign(seed, leaf_index, message))
    except (ValueError, RuntimeError):
        result = None
    write_case("xmss", HANDLER, case, {
        "input": {
            "seed":       hex_str(seed),
            "leaf_index": leaf_index,
            "message":    hex_str(message),
        },
        "output": result,
    })


@F.slow
def test_known_answer() -> None:
    _emit(f"{HANDLER}_known_answer",
          F.SEED_KNOWN_ANSWER, F.LEAF_KNOWN_ANSWER, F.MESSAGE_KNOWN_ANSWER)


@F.slow
def test_first_leaf() -> None:
    _emit(f"{HANDLER}_first_leaf",
          F.SEED_KNOWN_ANSWER, F.LEAF_FIRST, F.MESSAGE_KNOWN_ANSWER)


@F.slow
def test_second_tree() -> None:
    _emit(f"{HANDLER}_second_tree",
          F.SEED_KNOWN_ANSWER, F.LEAF_SECOND_TREE, F.MESSAGE_KNOWN_ANSWER)


@F.slow
def test_last_leaf() -> None:
    _emit(f"{HANDLER}_last_leaf",
          F.SEED_KNOWN_ANSWER, F.LEAF_LAST, F.MESSAGE_KNOWN_ANSWER)


def test_short_message() -> None:
    # 31 bytes: rejected before any tree is built.
    _emit(f"{HANDLER}_short_message",
          F.SEED_KNOWN_ANSWER, F.LEAF_FIRST, F.MESSAGE_KNOWN_ANSWER[:31])


def test_short_seed() -> None:
    _emit(f"{HANDLER}_short_seed",
          F.SEED_KNOWN_ANSWER[:31], F.LEAF_FIRST, F.MESSAGE_KNOWN_ANSWER)
