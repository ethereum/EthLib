"""The genesis blocks of the blockchain tests and of mainnet, through the bindings."""

import json

import pytest

import archives
from ethlib.cryptography.keccak import keccak256
from ethlib.errors import BlockError
from ethlib.execution import blocks
from ethlib.serialization import rlp
from parity.runners import genesis_of
from raising import raises
from transactions.test_transactions import FORK_OF_NETWORK

CASES = json.loads((archives.REPO / "tests" / "execution" / "blocks" / "genesis.json").read_text())
MAINNET = archives.REPO / "tests" / "execution" / "genesis" / "mainnet.json"
HASHES = (
    archives.REPO
    / "tests"
    / "execution"
    / "ethereum_tests"
    / "BasicTests"
    / "genesishashestest.json"
)


@pytest.mark.parametrize("case", CASES, ids=lambda case: case["network"])
def test_genesis_of_each_fork(case) -> None:
    fork = FORK_OF_NETWORK[case["network"]]
    block = genesis_of(fork, case["genesisBlockHeader"], case["pre"])
    assert block.hex() == case["genesisRLP"]
    assert (
        "0x" + keccak256(rlp.encode(rlp.decode(block)[0])).hex()
        == case["genesisBlockHeader"]["hash"]
    )


def test_mainnet() -> None:
    genesis = json.loads(MAINNET.read_text())
    expected = json.loads(HASHES.read_text())
    state = rlp.encode(
        [
            [
                bytes.fromhex(address[2:]),
                b"",
                int(a["balance"], 16).to_bytes(32, "big").lstrip(b"\0"),
                b"",
                [],
            ]
            for address, a in genesis["alloc"].items()
        ]
    )
    block = blocks.genesis_block(
        "frontier",
        state,
        coinbase=bytes.fromhex(genesis["coinbase"][2:]),
        difficulty=int(genesis["difficulty"], 16),
        gas_limit=int(genesis["gasLimit"], 16),
        timestamp=int(genesis["timestamp"], 16),
        extra_data=bytes.fromhex(genesis["extraData"][2:]),
        mix_hash=bytes.fromhex(genesis["mixHash"][2:]),
        nonce=int(genesis["nonce"], 16).to_bytes(8, "big"),
    )
    assert block.hex() == expected["genesis_rlp_hex"]
    assert rlp.decode(block)[0][3].hex() == expected["genesis_state_root"]
    assert keccak256(rlp.encode(rlp.decode(block)[0])).hex() == expected["genesis_hash"]


def test_fields_that_do_not_decode() -> None:
    # A nonce of 9 bytes is not a header nonce, so the export rejects the fields with code 0.
    with raises(
        BlockError,
        (
            "genesis fields rejected: EthLib.Serialization.Rlp.RlpError.inField 6 "
            "(EthLib.Serialization.Rlp.RlpError.wrongLength 8 9)"
        ),
    ) as error:
        blocks.genesis_block(
            "frontier",
            rlp.encode([]),
            coinbase=bytes(20),
            difficulty=1,
            gas_limit=5000,
            timestamp=0,
            extra_data=b"",
            mix_hash=bytes(32),
            nonce=bytes(9),
        )
    assert error.value.code == 0
