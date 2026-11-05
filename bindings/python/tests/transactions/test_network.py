"""The network form of blob transactions, built from blobs and proofs of the KZG bindings."""

# No upstream suite holds network forms, so each case is built here.
# The KZG bindings that make the commitments and the proofs run their own pinned vectors.

import hashlib
from functools import cache

import pytest

from ethlib.cryptography import keccak, kzg
from ethlib.execution import transactions
from ethlib.serialization import rlp


def _blob(seed: int) -> bytes:
    """A blob whose field elements are small integers, so each one is below the modulus."""
    return b"".join((seed + i).to_bytes(32, "big") for i in range(kzg.FIELD_ELEMENTS_PER_BLOB))


def _versioned_hash(commitment: bytes) -> bytes:
    return b"\x01" + hashlib.sha256(commitment).digest()[1:]


def _int(n: int) -> bytes:
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def _body(hashes: list[bytes]) -> list:
    """The fourteen fields of a blob transaction, with a dummy signature."""
    return [
        _int(1),
        _int(0),
        _int(1),
        _int(10),
        _int(21000),
        b"\x11" * 20,
        _int(0),
        b"",
        [],
        _int(1),
        hashes,
        _int(0),
        _int(1),
        _int(1),
    ]


@cache
def _blobs() -> tuple[list[bytes], list[bytes]]:
    blobs = [_blob(1), _blob(2)]
    return blobs, [kzg.blob_to_kzg_commitment(b) for b in blobs]


@cache
def _blob_proofs() -> list[bytes]:
    blobs, commitments = _blobs()
    return [kzg.compute_blob_kzg_proof(b, c) for b, c in zip(blobs, commitments)]


@cache
def _cell_proofs() -> list[bytes]:
    blobs, _ = _blobs()
    return [p for b in blobs for p in kzg.compute_cells_and_kzg_proofs(b)[1]]


def _dencun(body: list, blobs: list[bytes], commitments: list[bytes], proofs: list[bytes]) -> bytes:
    return b"\x03" + rlp.encode([body, blobs, commitments, proofs])


def _fusaka(
    body: list, blobs: list[bytes], commitments: list[bytes], proofs: list[bytes], version: int = 1
) -> bytes:
    return b"\x03" + rlp.encode([body, _int(version), blobs, commitments, proofs])


def _check_raises(fork: str, network: bytes, code: int) -> None:
    with pytest.raises(transactions.TransactionError) as info:
        transactions.network_check(fork, network)
    assert info.value.code == code


def test_dencun() -> None:
    blobs, commitments = _blobs()
    body = _body([_versioned_hash(c) for c in commitments])
    tx = transactions.network_check("dencun", _dencun(body, blobs, commitments, _blob_proofs()))
    # The transaction alone is the type, then the fourteen fields, as a block holds it.
    assert tx == b"\x03" + rlp.encode(body)
    assert transactions.tx_hash("dencun", tx) == keccak.keccak256(tx)


def test_fusaka() -> None:
    blobs, commitments = _blobs()
    body = _body([_versioned_hash(c) for c in commitments])
    assert len(_cell_proofs()) == kzg.CELLS_PER_EXT_BLOB * len(blobs)
    tx = transactions.network_check("fusaka", _fusaka(body, blobs, commitments, _cell_proofs()))
    assert tx == b"\x03" + rlp.encode(body)


def test_form_of_the_other_fork() -> None:
    blobs, commitments = _blobs()
    body = _body([_versioned_hash(c) for c in commitments])
    # Each fork reads only its own list: four items before Fusaka, five from it.
    _check_raises("fusaka", _dencun(body, blobs, commitments, _blob_proofs()), 3)
    _check_raises("dencun", _fusaka(body, blobs, commitments, _cell_proofs()), 3)


def test_before_dencun() -> None:
    blobs, commitments = _blobs()
    body = _body([_versioned_hash(c) for c in commitments])
    _check_raises("shapella", _dencun(body, blobs, commitments, _blob_proofs()), 2)


def test_wrong_version() -> None:
    blobs, commitments = _blobs()
    body = _body([_versioned_hash(c) for c in commitments])
    _check_raises("fusaka", _fusaka(body, blobs, commitments, _cell_proofs(), version=2), 101)


def test_count_mismatch() -> None:
    blobs, commitments = _blobs()
    body = _body([_versioned_hash(c) for c in commitments])
    _check_raises("dencun", _dencun(body, blobs, commitments, _blob_proofs()[:1]), 102)
    _check_raises("fusaka", _fusaka(body, blobs, commitments, _cell_proofs()[:-1]), 102)
    _check_raises(
        "dencun",
        _dencun(_body([_versioned_hash(commitments[0])]), blobs, commitments, _blob_proofs()),
        102,
    )


def test_versioned_hash_mismatch() -> None:
    blobs, commitments = _blobs()
    body = _body([_versioned_hash(c) for c in reversed(commitments)])
    _check_raises("dencun", _dencun(body, blobs, commitments, _blob_proofs()), 103)


def test_proof_rejected() -> None:
    blobs, commitments = _blobs()
    body = _body([_versioned_hash(c) for c in commitments])
    _check_raises("dencun", _dencun(body, blobs, commitments, _blob_proofs()[::-1]), 105)
    proofs = _cell_proofs()
    swapped = proofs[1:2] + proofs[:1] + proofs[2:]
    _check_raises("fusaka", _fusaka(body, blobs, commitments, swapped), 105)
