"""Test-vector generator: `verify` and `verify_low_s`.

Every case comes from a Wycheproof set, and its expected result is Wycheproof's.

- `verify`: the IEEE P1363 set, with 64-byte signatures, checked by ECDSA alone.
- `verify_low_s`: the Bitcoin set, checked by ECDSA and the low-s rule of EIP-2.

A Bitcoin signature that is not strict DER never reaches EthLib.
Its test still runs, and Wycheproof must call it invalid, but it writes no case.
"""

import pytest

from ethlib.cryptography import secp256k1

from . import wycheproof as W
from dumper import hex_str, write_case


def _verify(public_key: bytes, msg_hash: bytes, signature: bytes) -> bool | None:
    # A signature of the wrong length is rejected, written as a null output.
    try:
        return secp256k1.verify(public_key, msg_hash, signature)
    except ValueError:
        return None


def _write(handler: str, case: str, public_key: bytes, msg_hash: bytes, signature: bytes,
           result: bool | None) -> None:
    write_case("secp256k1", handler, case, {
        "input": {
            "public_key": hex_str(public_key),
            "msg_hash": hex_str(msg_hash),
            "signature": hex_str(signature),
        },
        "output": result,
    })


P1363 = list(W.cases(W.P1363))
BITCOIN = list(W.cases(W.BITCOIN))


@pytest.mark.parametrize("tc_id, public_key, msg_hash, signature, valid", P1363,
                         ids=[f"tc{c[0]}" for c in P1363])
def test_p1363(tc_id, public_key, msg_hash, signature, valid) -> None:
    result = _verify(public_key, msg_hash, signature)
    # A rejection, whether by length or by ECDSA, matches an invalid test.
    assert bool(result) == valid
    _write("verify", f"verify_wycheproof_p1363_{tc_id}", public_key, msg_hash, signature, result)


@pytest.mark.parametrize("tc_id, public_key, msg_hash, der, valid", BITCOIN,
                         ids=[f"tc{c[0]}" for c in BITCOIN])
def test_bitcoin(tc_id, public_key, msg_hash, der, valid) -> None:
    signature = W.der_signature(der)
    if signature is None:
        # Not strict DER: no signature to check, so Wycheproof must reject it.
        assert not valid
        return
    result = secp256k1.verify(public_key, msg_hash, signature) and secp256k1.is_low_s(signature)
    assert result == valid
    _write("verify_low_s", f"verify_low_s_wycheproof_bitcoin_{tc_id}", public_key, msg_hash, signature, result)


def test_high_s_verifies() -> None:
    # ECDSA accepts `(r, n - s)` with `(r, s)`, and the low-s rule tells them apart.
    n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
    tc_id, public_key, msg_hash, signature, valid = next(c for c in P1363 if c[4])
    r, s = signature[:32], int.from_bytes(signature[32:], "big")
    flipped = r + (n - s).to_bytes(32, "big")
    assert secp256k1.verify(public_key, msg_hash, flipped)
    assert secp256k1.is_low_s(signature) != secp256k1.is_low_s(flipped)
