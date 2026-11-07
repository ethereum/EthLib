"""Test-vector generator: `sign`."""

from dumper import hex_str, write_case
from ethlib.cryptography import xmss

from . import fixtures

HANDLER = "sign"


def _emit(case: str, seed: bytes, leaf_index: int, message: bytes) -> None:
    # Inputs of the wrong length are rejected, written as a null output.
    try:
        result = hex_str(xmss.sign(seed, leaf_index, message))
    except (ValueError, RuntimeError):
        result = None
    write_case(
        "xmss",
        HANDLER,
        case,
        {
            "input": {
                "seed": hex_str(seed),
                "leaf_index": leaf_index,
                "message": hex_str(message),
            },
            "output": result,
        },
    )


@fixtures.slow
def test_known_answer() -> None:
    _emit(
        f"{HANDLER}_known_answer",
        fixtures.SEED_KNOWN_ANSWER,
        fixtures.LEAF_KNOWN_ANSWER,
        fixtures.MESSAGE_KNOWN_ANSWER,
    )


@fixtures.slow
def test_first_leaf() -> None:
    _emit(
        f"{HANDLER}_first_leaf",
        fixtures.SEED_KNOWN_ANSWER,
        fixtures.LEAF_FIRST,
        fixtures.MESSAGE_KNOWN_ANSWER,
    )


@fixtures.slow
def test_second_tree() -> None:
    _emit(
        f"{HANDLER}_second_tree",
        fixtures.SEED_KNOWN_ANSWER,
        fixtures.LEAF_SECOND_TREE,
        fixtures.MESSAGE_KNOWN_ANSWER,
    )


@fixtures.slow
def test_last_leaf() -> None:
    _emit(
        f"{HANDLER}_last_leaf",
        fixtures.SEED_KNOWN_ANSWER,
        fixtures.LEAF_LAST,
        fixtures.MESSAGE_KNOWN_ANSWER,
    )


def test_short_message() -> None:
    # 31 bytes: rejected before any tree is built.
    _emit(
        f"{HANDLER}_short_message",
        fixtures.SEED_KNOWN_ANSWER,
        fixtures.LEAF_FIRST,
        fixtures.MESSAGE_KNOWN_ANSWER[:-1],
    )


def test_short_seed() -> None:
    _emit(
        f"{HANDLER}_short_seed",
        fixtures.SEED_KNOWN_ANSWER[:-1],
        fixtures.LEAF_FIRST,
        fixtures.MESSAGE_KNOWN_ANSWER,
    )
