"""Test-vector generator: `key_gen`."""

from ethlib.cryptography import keccak, sphincs

from . import fixtures as F
from dumper import hex_str, write_case


HANDLER = "key_gen"


def _emit(case: str, seed: bytes) -> None:
    # A seed of any other length is rejected, written as a null output.
    try:
        result = hex_str(sphincs.key_gen(seed))
    except (ValueError, RuntimeError):
        result = None
    write_case("sphincs", HANDLER, case, {
        "input": {"seed": hex_str(seed)},
        "output": result,
    })


@F.slow
def test_known_answer() -> None:
    _emit(f"{HANDLER}_known_answer", F.SEED_KNOWN_ANSWER)


@F.slow
def test_zero_seed() -> None:
    _emit(f"{HANDLER}_zero_seed", F.SEED_ZERO)


def test_short_seed() -> None:
    # 31 bytes: rejected before any hashing.
    _emit(f"{HANDLER}_short_seed", F.SEED_KNOWN_ANSWER[:31])


def test_long_seed() -> None:
    # 33 bytes: rejected, never truncated.
    _emit(f"{HANDLER}_long_seed", F.SEED_KNOWN_ANSWER + b"\x00")


def test_scheme_seed() -> None:
    # The hash of the name, then the seed, that key generation starts with.
    # It checks the value through the Keccak-256 binding, not through key generation itself.
    assert keccak.keccak256(b"leanSPHINCS" + F.SEED_KNOWN_ANSWER) == F.SCHEME_SEED_KNOWN_ANSWER
