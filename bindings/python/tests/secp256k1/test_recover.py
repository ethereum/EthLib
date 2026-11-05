"""Test-vector generator: `recover`.

For each valid signature of the Wycheproof P1363 set,
one of the recovery ids 0 and 1 must return the test's public key.

The exception is a signature whose `R` has `x = r + n`, possible only when `r + n < p`.
Only the ids 2 and 3 reach that `R`, and Ethereum does not use them.
Wycheproof builds two such signatures, tests 115 and 247.

Each id writes a case: the key it returns, or null when it returns none.
"""

import pytest

from dumper import hex_str, write_case
from ethlib.cryptography import secp256k1
from raising import raises

from . import wycheproof

VALID = [c for c in wycheproof.cases(wycheproof.P1363) if c[4]]

# The field modulus and the group order, from SEC 2 v2 §2.4.1.
P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141


def _recover(msg_hash: bytes, signature: bytes, recovery_id: int) -> bytes | None:
    # No point `R` with that parity, or a key at infinity, is a rejection.
    try:
        return secp256k1.recover(msg_hash, signature, recovery_id)
    except ValueError:
        return None


@pytest.mark.parametrize(
    "tc_id, public_key, msg_hash, signature, valid", VALID, ids=[f"tc{c[0]}" for c in VALID]
)
def test_recover(tc_id, public_key, msg_hash, signature, valid) -> None:
    keys = [_recover(msg_hash, signature, i) for i in (0, 1)]
    # The signer's key is among the two, unless `R` may have `x = r + n`.
    r = int.from_bytes(signature[:32], "big")
    assert public_key in keys or r + N < P
    # The two ids never give the same key.
    assert keys[0] is None or keys[1] is None or keys[0] != keys[1]
    # Every key recovered verifies the signature.
    for key in keys:
        assert key is None or secp256k1.verify(key, msg_hash, signature)
    for i, key in enumerate(keys):
        write_case(
            "secp256k1",
            "recover",
            f"recover_wycheproof_p1363_{tc_id}_{i}",
            {
                "input": {
                    "msg_hash": hex_str(msg_hash),
                    "signature": hex_str(signature),
                    "recovery_id": i,
                },
                "output": None if key is None else hex_str(key),
            },
        )


def test_recovery_id_out_of_range() -> None:
    _, _, msg_hash, signature, _ = VALID[0]
    with raises(ValueError, "bad recovery id: 2, expected 0 or 1"):
        secp256k1.recover(msg_hash, signature, 2)
