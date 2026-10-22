"""
Constant inputs (blobs, field elements, points, cells) shared by every
KZG test-vector generator.
"""

from functools import lru_cache

from py_ecc import optimized_bls12_381 as bls
from py_ecc.bls.g2_primitives import G1_to_pubkey, pubkey_to_G1

from ethlib.cryptography import kzg


# ---- Memoized spec calls --------------------------------------------------

@lru_cache(maxsize=None)
def cached_cells_and_proofs(blob: bytes) -> tuple[tuple[bytes, ...], tuple[bytes, ...]]:
    cells, proofs = kzg.compute_cells_and_kzg_proofs(blob)
    return tuple(cells), tuple(proofs)


@lru_cache(maxsize=None)
def cached_commitment(blob: bytes) -> bytes:
    return kzg.blob_to_kzg_commitment(blob)


@lru_cache(maxsize=None)
def cached_kzg_proof(blob: bytes, z: bytes) -> tuple[bytes, bytes]:
    return kzg.compute_kzg_proof(blob, z)


@lru_cache(maxsize=None)
def cached_blob_kzg_proof(blob: bytes, commitment: bytes) -> bytes:
    return kzg.compute_blob_kzg_proof(blob, commitment)

# ---- Field arithmetic ------------------------------------------------------

BLS_MODULUS = bls.curve_order
PRIMITIVE_ROOT_OF_UNITY = 7


def field_element_bytes(x: int) -> bytes:
    assert 0 <= x < BLS_MODULUS
    return int.to_bytes(x, 32, "big")


def field_element_bytes_unchecked(x: int) -> bytes:
    return int.to_bytes(x, 32, "big")


def _root_of_unity(order: int) -> int:
    """Primitive `order`-th root of unity in the BLS12-381 scalar field."""
    assert (BLS_MODULUS - 1) % order == 0
    return pow(PRIMITIVE_ROOT_OF_UNITY, (BLS_MODULUS - 1) // order, BLS_MODULUS)


# ---- BLS group helpers (compressed form) ----------------------------------

# Compressed G1 generator (canonical encoding from the BLS12-381 spec).
G1 = G1_to_pubkey(bls.G1)

# Compressed point at infinity on G1.
G1_POINT_AT_INFINITY = G1_to_pubkey(bls.Z1)


def bls_add_one(x: bytes) -> bytes:
    """Compressed-G1 addition `x + G1_generator`. Used to fabricate
    intentionally-incorrect proofs in the verify-* generators. Implemented
    via `py_ecc` so the spec module doesn't need to expose a curve-add
    primitive purely for negative-test fixtures."""
    return G1_to_pubkey(bls.add(pubkey_to_G1(x), bls.G1))


# ---- Field elements -------------------------------------------------------

FE_VALID1 = field_element_bytes(0)
FE_VALID2 = field_element_bytes(1)
FE_VALID3 = field_element_bytes(2)
FE_VALID4 = field_element_bytes(pow(5, 1235, BLS_MODULUS))
FE_VALID5 = field_element_bytes(BLS_MODULUS - 1)
# Primitive (FIELD_ELEMENTS_PER_BLOB)-th root of unity — `roots[1]`.
FE_VALID6 = field_element_bytes(_root_of_unity(kzg.FIELD_ELEMENTS_PER_BLOB))

VALID_FIELD_ELEMENTS = [FE_VALID1, FE_VALID2, FE_VALID3, FE_VALID4, FE_VALID5, FE_VALID6]

BLS_MODULUS_BYTES = field_element_bytes_unchecked(BLS_MODULUS)

FE_INVALID_EQUAL_TO_MODULUS = BLS_MODULUS_BYTES
FE_INVALID_MODULUS_PLUS_ONE = field_element_bytes_unchecked(BLS_MODULUS + 1)
FE_INVALID_UINT256_MAX      = field_element_bytes_unchecked(2**256 - 1)
FE_INVALID_UINT256_MID      = field_element_bytes_unchecked(2**256 - 2**128)
FE_INVALID_LENGTH_PLUS_ONE  = FE_VALID1 + b"\x00"
FE_INVALID_LENGTH_MINUS_ONE = FE_VALID1[:-1]

INVALID_FIELD_ELEMENTS = [
    FE_INVALID_EQUAL_TO_MODULUS,
    FE_INVALID_MODULUS_PLUS_ONE,
    FE_INVALID_UINT256_MAX,
    FE_INVALID_UINT256_MID,
    FE_INVALID_LENGTH_PLUS_ONE,
    FE_INVALID_LENGTH_MINUS_ONE,
]


# ---- Blobs ----------------------------------------------------------------

_FE_PER_BLOB = kzg.FIELD_ELEMENTS_PER_BLOB

BLOB_ALL_ZEROS = bytes(kzg.BYTES_PER_BLOB)
BLOB_ALL_TWOS = b"".join(field_element_bytes(2) for _ in range(_FE_PER_BLOB))
BLOB_RANDOM_VALID1 = b"".join(
    field_element_bytes(pow(2, n + 256, BLS_MODULUS)) for n in range(_FE_PER_BLOB)
)
BLOB_RANDOM_VALID2 = b"".join(
    field_element_bytes(pow(3, n + 256, BLS_MODULUS)) for n in range(_FE_PER_BLOB)
)
BLOB_RANDOM_VALID3 = b"".join(
    field_element_bytes(pow(5, n + 256, BLS_MODULUS)) for n in range(_FE_PER_BLOB)
)
BLOB_ALL_MODULUS_MINUS_ONE = b"".join(
    field_element_bytes(BLS_MODULUS - 1) for _ in range(_FE_PER_BLOB)
)
BLOB_ALMOST_ZERO = b"".join(
    field_element_bytes(1 if n == 3211 else 0) for n in range(_FE_PER_BLOB)
)

BLOB_INVALID = b"\xff" * kzg.BYTES_PER_BLOB
BLOB_INVALID_CLOSE = b"".join(
    BLS_MODULUS_BYTES if n == 2111 else field_element_bytes(0)
    for n in range(_FE_PER_BLOB)
)
BLOB_INVALID_LENGTH_PLUS_ONE  = BLOB_RANDOM_VALID1 + b"\x00"
BLOB_INVALID_LENGTH_MINUS_ONE = BLOB_RANDOM_VALID1[:-1]

VALID_BLOBS = [
    BLOB_ALL_ZEROS,
    BLOB_ALL_TWOS,
    BLOB_RANDOM_VALID1,
    BLOB_RANDOM_VALID2,
    BLOB_RANDOM_VALID3,
    BLOB_ALL_MODULUS_MINUS_ONE,
    BLOB_ALMOST_ZERO,
]
INVALID_BLOBS = [
    BLOB_INVALID,
    BLOB_INVALID_CLOSE,
    BLOB_INVALID_LENGTH_PLUS_ONE,
    BLOB_INVALID_LENGTH_MINUS_ONE,
]


# ---- Compressed G1 inputs --------------------------------------------------

G1_INVALID_TOO_FEW_BYTES   = G1[:-1]
G1_INVALID_TOO_MANY_BYTES  = G1 + b"\x00"
G1_INVALID_P1_NOT_IN_G1    = bytes.fromhex(
    "8123456789abcdef0123456789abcdef0123456789abcdef"
    "0123456789abcdef0123456789abcdef0123456789abcdef"
)
G1_INVALID_P1_NOT_ON_CURVE = bytes.fromhex(
    "8123456789abcdef0123456789abcdef0123456789abcdef"
    "0123456789abcdef0123456789abcdef0123456789abcde0"
)
INVALID_G1_POINTS = [
    G1_INVALID_TOO_FEW_BYTES,
    G1_INVALID_TOO_MANY_BYTES,
    G1_INVALID_P1_NOT_IN_G1,
    G1_INVALID_P1_NOT_ON_CURVE,
]


# ---- Cells ----------------------------------------------------------------

_FE_PER_CELL = kzg.FIELD_ELEMENTS_PER_CELL

CELL_RANDOM_VALID1 = b"".join(
    field_element_bytes(pow(2, n + 256, BLS_MODULUS)) for n in range(_FE_PER_CELL)
)
CELL_RANDOM_VALID2 = b"".join(
    field_element_bytes(pow(3, n + 256, BLS_MODULUS)) for n in range(_FE_PER_CELL)
)
CELL_RANDOM_VALID3 = b"".join(
    field_element_bytes(pow(5, n + 256, BLS_MODULUS)) for n in range(_FE_PER_CELL)
)
CELL_ALL_MAX_VALUE = b"".join(
    field_element_bytes_unchecked(2**256 - 1) for _ in range(_FE_PER_CELL)
)
CELL_ONE_INVALID_FIELD = b"".join(
    BLS_MODULUS_BYTES if n == 7 else field_element_bytes(0) for n in range(_FE_PER_CELL)
)
CELL_INVALID_TOO_FEW_BYTES  = CELL_RANDOM_VALID1[:-1]
CELL_INVALID_TOO_MANY_BYTES = CELL_RANDOM_VALID2 + b"\x00"

VALID_INDIVIDUAL_RANDOM_CELL_BYTES = [CELL_RANDOM_VALID1, CELL_RANDOM_VALID2, CELL_RANDOM_VALID3]
INVALID_INDIVIDUAL_CELL_BYTES = [
    CELL_ALL_MAX_VALUE,
    CELL_ONE_INVALID_FIELD,
    CELL_INVALID_TOO_FEW_BYTES,
    CELL_INVALID_TOO_MANY_BYTES,
]


# ---- Cell helpers ---------------------------------------------------------

def cell_to_coset_evals(cell: bytes) -> list[bytes]:
    """Split a cell into its 64 field-element-bytes — the form the
    `compute_verify_cell_kzg_proof_batch_challenge` generator passes as
    each entry of `cosets_evals`. The Lean impl of `compute_cells`
    stores cells in the same byte order the challenge function
    consumes, so this is just a 32-byte chunk-up."""
    return [cell[i*32:(i+1)*32] for i in range(_FE_PER_CELL)]
