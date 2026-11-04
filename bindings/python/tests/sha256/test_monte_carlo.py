"""SHA-256 against the Monte Carlo test of NIST CAVP, `cavp/SHA256Monte.rsp`."""

import hashlib
from pathlib import Path

from ethlib.cryptography.sha256 import sha256

MONTE = Path(__file__).resolve().parent / "cavp" / "SHA256Monte.rsp"


def _read() -> tuple[bytes, list[bytes]]:
    """The seed and the 100 checkpoint digests of the file, in order."""
    seed, checkpoints = None, []
    for line in MONTE.read_text().splitlines():
        key, sep, value = line.partition(" = ")
        if key.strip() == "Seed":
            seed = bytes.fromhex(value.strip())
        elif key.strip() == "COUNT":
            assert int(value) == len(checkpoints)
        elif key.strip() == "MD":
            checkpoints.append(bytes.fromhex(value.strip()))
    assert seed is not None and len(checkpoints) == 100
    return seed, checkpoints


def test_monte_carlo() -> None:
    # SHAVS §6.4: each checkpoint hashes 1000 messages, each the last three digests joined,
    # and the last digest is the seed of the next checkpoint.
    seed, checkpoints = _read()
    for j, expected in enumerate(checkpoints):
        md = [seed, seed, seed]
        for _ in range(1000):
            md = [md[1], md[2], sha256(md[0] + md[1] + md[2])]
        seed = md[2]
        assert seed == expected, f"checkpoint {j}"


def test_procedure_agrees_with_hashlib() -> None:
    # The same chain with hashlib's SHA-256 meets the first checkpoint, so the loop above follows
    # SHAVS and the file is read right.
    seed, checkpoints = _read()
    md = [seed, seed, seed]
    for _ in range(1000):
        md = [md[1], md[2], hashlib.sha256(md[0] + md[1] + md[2]).digest()]
    assert md[2] == checkpoints[0]
