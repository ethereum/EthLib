"""The AES block cipher against the ECB Monte Carlo test of NIST CAVP (AESAVS)."""

import os
from pathlib import Path

import pytest

from ethlib.cryptography import aes

CAVP = Path(__file__).resolve().parent / "cavp"

# Each section has 100 checkpoints of 1000 block operations.
# The pull-request tier runs the first PR_CHECKPOINTS of each section.
# The weekly tier runs all of them.
CHECKPOINTS = 100
PR_CHECKPOINTS = 10
SLOW = os.environ.get("ETHLIB_SLOW_VECTORS") == "1"


def _sections(bits: int) -> dict[str, list[tuple[bytes, bytes, bytes]]]:
    """The (key, plaintext, ciphertext) checkpoints of the encrypt and the decrypt section."""
    sections: dict[str, list] = {}
    direction, case = "", {}
    for line in (CAVP / f"ECBMCT{bits}.rsp").read_text().splitlines():
        line = line.strip()
        if line in ("[ENCRYPT]", "[DECRYPT]"):
            direction = line[1:-1]
            sections[direction] = []
            continue
        key, sep, value = line.partition(" = ")
        if not sep:
            continue
        case[key] = value
        # The last field of a checkpoint is the output of its direction.
        if key == ("CIPHERTEXT" if direction == "ENCRYPT" else "PLAINTEXT"):
            assert int(case["COUNT"]) == len(sections[direction])
            sections[direction].append(
                tuple(bytes.fromhex(case[k]) for k in ("KEY", "PLAINTEXT", "CIPHERTEXT"))
            )
            case = {}
    return sections


@pytest.mark.parametrize("bits", [128, 256])
@pytest.mark.parametrize("direction", ["ENCRYPT", "DECRYPT"])
def test_monte_carlo(bits: int, direction: str) -> None:
    # AESAVS §6.4.1: each checkpoint starts from its key and input.
    # Each of its 1000 operations feeds its output to the next.
    # The last output is the checkpoint's answer and the next checkpoint's input.
    # The next key is the key XOR the last output.
    # A 256-bit key takes the last two outputs.
    checkpoints = _sections(bits)[direction]
    assert len(checkpoints) == CHECKPOINTS
    run = aes.encrypt_block if direction == "ENCRYPT" else aes.decrypt_block
    count = CHECKPOINTS if SLOW else PR_CHECKPOINTS
    key, plaintext, ciphertext = checkpoints[0]
    text = plaintext if direction == "ENCRYPT" else ciphertext
    for i in range(count):
        expected_key, plaintext, ciphertext = checkpoints[i]
        source, target = (
            (plaintext, ciphertext) if direction == "ENCRYPT" else (ciphertext, plaintext)
        )
        assert key == expected_key and text == source, f"checkpoint {i}"
        previous = text
        for _ in range(1000):
            previous, text = text, run(key, text)
        assert text == target, f"checkpoint {i}"
        tail = text if bits == 128 else previous + text
        key = bytes(a ^ b for a, b in zip(key, tail, strict=True))
