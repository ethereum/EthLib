"""The EIP-8450 proof of possession, against possession roots of an independent SSZ."""

import os
from functools import cache
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.cryptography import xmss
from ethlib.errors import ConsensusError

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "pq_keys" / "possession"

CASES = sorted(path.name for path in FILES.iterdir())

# Signing builds two trees of 2^16 one-time keys, which takes minutes, so it runs only on request.
slow = pytest.mark.skipif(os.environ.get("ETHLIB_SLOW_VECTORS") != "1",
                          reason="set ETHLIB_SLOW_VECTORS=1 to sign again")


def _load(path: Path) -> dict:
    """The values of a YAML file, with each hex string as bytes."""
    data = YAML(typ="safe").load(path.read_text())
    return {key: bytes.fromhex(value[2:]) if value.startswith("0x") else value
            for key, value in data.items()}


@cache
def _case(name: str) -> dict:
    """The inputs and the root of a case, with the proofs that EthLib signed for it."""
    return _load(FILES / name / "data.yaml") | _load(FILES / name / "proof.yaml")


def _valid(case: dict, proof: bytes, pubkey: bytes | None = None, name: str | None = None) -> bool:
    """Whether Lean accepts a proof for a case, for its BLS key and configuration or others."""
    return consensus.pq_keys_is_valid_possession_proof(
        case["genesis_validators_root"], case["pubkey"] if pubkey is None else pubkey,
        case["xmss_public_key"], proof, case["config"] if name is None else name)


@pytest.mark.parametrize("name", CASES)
def test_signing_root(name):
    case = _case(name)
    assert consensus.pq_keys_possession_signing_root(
        case["genesis_validators_root"], case["pubkey"], case["xmss_public_key"],
        case["config"]) == case["signing_root"]


@pytest.mark.parametrize("name", CASES)
def test_honest_proof_is_valid(name):
    case = _case(name)
    assert xmss.signature_index(case["proof"]) == 0
    assert xmss.verify(case["xmss_public_key"], case["signing_root"], case["proof"])
    assert _valid(case, case["proof"])


def test_proof_at_another_leaf_is_rejected():
    case = _case("mainnet_genesis_root")
    proof = case["proof_at_leaf_1"]
    assert xmss.signature_index(proof) == 1
    assert xmss.verify(case["xmss_public_key"], case["signing_root"], proof)
    assert not _valid(case, proof)


def test_proof_for_another_bls_key_is_rejected():
    case = _case("mainnet_genesis_root")
    other = _case("mainnet_other_pubkey")
    assert case["xmss_public_key"] == other["xmss_public_key"]
    assert not _valid(case, other["proof"])
    assert not _valid(other, case["proof"])


def test_proof_for_another_chain_is_rejected():
    case = _case("mainnet_genesis_root")
    zero = _case("mainnet_zero_root")
    assert not _valid(case, zero["proof"])
    assert not _valid(zero, case["proof"])


def test_proof_for_another_configuration_is_rejected():
    mainnet = _case("mainnet_zero_root")
    minimal = _case("minimal_zero_root")
    assert not _valid(mainnet, mainnet["proof"], name="minimal")
    assert not _valid(minimal, minimal["proof"], name="mainnet")


def test_proof_under_another_key_is_rejected():
    case = _case("mainnet_genesis_root")
    other = _case("mainnet_other_key")
    assert case["xmss_public_key"] != other["xmss_public_key"]
    assert not _valid(case, other["proof"])


@pytest.mark.parametrize("position", [0, 4, 1203, 1204, 2403])
def test_tampered_proof_is_rejected(position):
    case = _case("mainnet_genesis_root")
    proof = bytearray(case["proof"])
    proof[position] ^= 1
    assert not _valid(case, bytes(proof))


def test_wrong_lengths_are_rejected():
    case = _case("mainnet_genesis_root")
    proof = case["proof"]
    with pytest.raises(ConsensusError):
        _valid(case, proof[:-1])
    with pytest.raises(ConsensusError):
        _valid(case, proof, pubkey=case["pubkey"][:-1])
    with pytest.raises(ConsensusError):
        consensus.pq_keys_possession_signing_root(
            case["genesis_validators_root"], case["pubkey"] + b"\x00", case["xmss_public_key"])
    with pytest.raises(ConsensusError):
        _valid(case, proof, name="holesky")


@slow
@pytest.mark.parametrize("name", CASES)
def test_proofs_are_signed_again(name):
    case = _case(name)
    assert xmss.key_gen(case["xmss_seed"]) == case["xmss_public_key"]
    assert xmss.sign(case["xmss_seed"], 0, case["signing_root"]) == case["proof"]
    if "proof_at_leaf_1" in case:
        assert xmss.sign(case["xmss_seed"], 1, case["signing_root"]) == case["proof_at_leaf_1"]
