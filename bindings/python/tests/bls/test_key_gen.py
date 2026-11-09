"""Validator key derivation against ERC-2333 and the paths of ERC-2334."""

import pytest
from py_ecc.bls import G2ProofOfPossession as RefBls
from py_ecc.optimized_bls12_381 import curve_order

from ethlib.cryptography import bls
from raising import raises

# ERC-2333 Test Cases 0 to 3: seed, master key, child index and child key.
#
# File: ERCS/erc-2333.md, Test Cases
# Repository: ethereum/ERCs
# Commit: be307c948f28897adb8f25afcc253c2c909de35d

ERC_2333 = [
    (
        "c55257c360c07c72029aebc1b53c05ed0362ada38ead3e3e9efa3708e53495531f09a6987599d18264"
        "c1e1c92f2cf141630c7a3c4ab7c81b2f001698e7463b04",
        6083874454709270928345386274498605044986640685124978867557563392430687146096,
        0,
        20397789859736650942317412262472558107875392172444076792671091975210932703118,
    ),
    (
        "3141592653589793238462643383279502884197169399375105820974944592",
        29757020647961307431480504535336562678282505419141012933316116377660817309383,
        3141592653,
        25457201688850691947727629385191704516744796114925897962676248250929345014287,
    ),
    (
        "0099FF991111002299DD7744EE3355BBDD8844115566CC55663355668888CC00",
        27580842291869792442942448775674722299803720648445448686099262467207037398656,
        4294967295,
        29358610794459428860402234341874281240803786294062035874021252734817515685787,
    ),
    (
        "d4e56740f876aef8c010b86a40d5f56745a118d0906a34e69aec8c0db1cb8fa3",
        19022158461524446591288038168518313374041767046816487870552872741050760015818,
        42,
        31372231650479070279774297061823572166496564838472787488249775572789064611981,
    ),
]


@pytest.mark.parametrize("seed, master_sk, child_index, child_sk", ERC_2333)
def test_erc2333_keys(seed: str, master_sk: int, child_index: int, child_sk: int) -> None:
    seed_bytes, master = bytes.fromhex(seed), master_sk.to_bytes(32, "big")
    assert bls.key_gen(seed_bytes) == master
    assert bls.derive_master_sk(seed_bytes) == master
    assert bls.derive_child_sk(master, child_index) == child_sk.to_bytes(32, "big")


@pytest.mark.parametrize("ikm", [b"\x00" * 32, bytes(range(32)), b"\xff" * 64])
@pytest.mark.parametrize("key_info", [b"", b"key info"])
def test_matches_reference(ikm: bytes, key_info: bytes) -> None:
    expected = RefBls.KeyGen(ikm, key_info)
    assert bls.key_gen(ikm, key_info) == expected.to_bytes(32, "big")


def test_rejects_short_input() -> None:
    with raises(bls.BlsError, "input keying material too short: 31 bytes") as error:
        bls.key_gen(b"\x01" * 31)
    assert (type(error.value), error.value.code) == (bls.BlsError, 14)
    with raises(bls.BlsError, "input keying material too short: 31 bytes") as error:
        bls.derive_master_sk(b"\x01" * 31)
    assert (type(error.value), error.value.code) == (bls.BlsError, 14)
    with raises(bls.BlsError, "input keying material too short: 31 bytes") as error:
        bls.derive_path(b"\x01" * 31, "m/12381/3600/0/0")
    assert (type(error.value), error.value.code) == (bls.KeyDerivationError, 14)


# ERC-2334 paths: at least four indices after `m`, purpose 12381, and the validator key paths.
#
# File: ERCS/erc-2334.md, Path and Beacon Chain Specific Parameters
# Repository: ethereum/ERCs
# Commit: be307c948f28897adb8f25afcc253c2c909de35d


@pytest.mark.parametrize(
    "path, indices",
    [
        ("m/12381/3600/0/0", [12381, 3600, 0, 0]),
        ("m/012381/03600/0000/0", [12381, 3600, 0, 0]),
        ("m/12381/3600/4294967295/0/0", [12381, 3600, 2**32 - 1, 0, 0]),
        ("m/12381/1/2/3/4/5", [12381, 1, 2, 3, 4, 5]),
    ],
)
def test_path_derivation(path: str, indices: list[int]) -> None:
    seed = bytes(range(32))
    key = bls.derive_master_sk(seed)
    for index in indices:
        key = bls.derive_child_sk(key, index)
    assert bls.derive_path(seed, path) == key


@pytest.mark.parametrize("index", [0, 2**32 - 1])
def test_validator_paths(index: int) -> None:
    assert bls.withdrawal_path(index) == f"m/12381/3600/{index}/0"
    assert bls.signing_path(index) == f"m/12381/3600/{index}/0/0"


def test_validator_paths_reject_bad_index() -> None:
    with raises(bls.KeyDerivationError, f"expected an int below {2**32}, got {2**32}") as error:
        bls.withdrawal_path(2**32)
    assert error.value.code == 0
    with raises(bls.KeyDerivationError, "expected an int") as error:
        bls.signing_path(True)
    assert error.value.code == 0


@pytest.mark.parametrize(
    "parent",
    [b"", bytes(31), bytes(33), bytes(32), curve_order.to_bytes(32, "big")],
)
def test_rejects_invalid_parent(parent: bytes) -> None:
    with raises(bls.BlsError, "invalid secret key") as error:
        bls.derive_child_sk(parent, 0)
    assert (type(error.value), error.value.code) == (bls.BlsError, 13)


def test_accepts_largest_parent() -> None:
    child = int.from_bytes(bls.derive_child_sk((curve_order - 1).to_bytes(32, "big"), 0), "big")
    assert 0 < child < curve_order


def test_rejects_index_out_of_range() -> None:
    parent = (1).to_bytes(32, "big")
    with raises(bls.BlsError, f"expected an int below {2**32}, got {2**32}") as error:
        bls.derive_child_sk(parent, 2**32)
    assert (type(error.value), error.value.code) == (bls.BlsError, 0)
    with raises(ValueError, "cannot pass a negative int to Lean"):
        bls.derive_child_sk(parent, -1)


@pytest.mark.parametrize(
    "path, code, message",
    [
        ("M/12381/3600/0/0", 101, "path must start with m"),
        ("m/12381/3600/0", 104, "ERC-2334 path needs at least four indices"),
        ("m/12380/3600/0/0", 105, "invalid path purpose: 12380"),
        ("m/12381/3600/0/0/", 102, "invalid path index: "),
        ("m/12381/3600/-1/0", 102, "invalid path index: -1"),
        ("m/12381/3600/0/0'", 102, "invalid path index: 0'"),
        ("m/12381/3600/0/x", 102, "invalid path index: x"),
        ("m/12381/3600/0/ 0", 102, "invalid path index:  0"),
        ("m/12381/3600/0/９", 102, "invalid path index: ９"),
        ("m/12381/3600/4294967296/0", 103, "path index out of range: 4294967296"),
    ],
)
def test_rejects_invalid_path(path: str, code: int, message: str) -> None:
    with raises(bls.KeyDerivationError, message) as error:
        bls.derive_path(bytes(32), path)
    assert error.value.code == code
    assert isinstance(error.value, bls.BlsError)


def test_rejects_wrong_types() -> None:
    parent = (1).to_bytes(32, "big")
    with raises(bls.BlsError, "expected bytes"):
        bls.derive_master_sk("seed")  # ty: ignore[invalid-argument-type]
    with raises(bls.BlsError, "expected bytes"):
        bls.derive_child_sk(1, 0)  # ty: ignore[invalid-argument-type]
    with raises(bls.KeyDerivationError, "expected a str"):
        bls.derive_path(bytes(32), b"m/12381/3600/0/0")  # ty: ignore[invalid-argument-type]
    with raises(bls.BlsError, "expected an int"):
        bls.derive_child_sk(parent, True)
