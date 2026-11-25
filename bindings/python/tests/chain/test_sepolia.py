"""The active fork, genesis block and fork IDs of Sepolia, against its pinned files and the EIPs."""

import json
import re

import pytest

import archives
from ethlib.chain import (
    ChainError,
    active_fork,
    chain_config,
    write_execution_config,
)
from ethlib.cryptography.keccak import keccak256
from ethlib.execution import blocks
from ethlib.networking import forkid
from ethlib.networking.forkid import BLOCK, TIME
from ethlib.serialization import rlp
from raising import raises

# The configuration files of Sepolia and the header of its last proof-of-work block.
#
# Files: metadata/genesis.json, metadata/config.yaml
# Repository: eth-clients/sepolia
# Commit: 7b1b9d9549787b6bbf538f943304c4cf84f7e39e
FILES = archives.REPO / "tests" / "execution" / "sepolia"
GENESIS = json.loads((FILES / "genesis.json").read_text())
CONFIG = (FILES / "config.yaml").read_text()
TERMINAL_HEADER = (FILES / "terminal_header.rlp").read_bytes()

# The first timestamp of each fork by time, with the fork before it.
# The genesis file gives the time of Shapella.
# The Sepolia rows of the "Activation" tables of four meta EIPs give the rest.
# They are EIP-7569, EIP-7600, EIP-7607 and EIP-7773.
# EIP-7607 also gives the fork hash at Fusaka, BPO1 and BPO2.
#
# Repository: ethereum/EIPs
# Commit: b055feec322fbc37e9d77a393a50b3ff56b31c92
TIMES = [
    (1_677_557_088, "paris", "shapella", "shanghaiTime"),
    (1_706_655_072, "shapella", "dencun", "cancunTime"),
    (1_741_159_776, "dencun", "pectra", "pragueTime"),
    (1_760_427_360, "pectra", "fusaka", "osakaTime"),
    (1_761_017_184, "fusaka", "bpo1", "bpo1Time"),
    (1_761_607_008, "bpo1", "bpo2", "bpo2Time"),
    (1_791_294_816, "bpo2", "glamsterdam", "amsterdamTime"),
]
FORK_HASHES = {
    1_760_427_360: bytes.fromhex("e2ae4999"),
    1_761_017_184: bytes.fromhex("56078a1e"),
    1_761_607_008: bytes.fromhex("268956b6"),
}

# The block keys of the genesis file, each with the fork it activates.
# EIP-155 and EIP-158 are both part of Spurious Dragon.
GENESIS_BLOCKS = [
    ("homesteadBlock", "homestead"),
    ("eip150Block", "tangerineWhistle"),
    ("eip155Block", "spuriousDragon"),
    ("eip158Block", "spuriousDragon"),
    ("byzantiumBlock", "byzantium"),
    ("constantinopleBlock", "constantinople"),
    ("petersburgBlock", "petersburg"),
    ("istanbulBlock", "istanbul"),
    ("berlinBlock", "berlin"),
    ("londonBlock", "london"),
]

# The blob schedule of each fork, as target, maximum and update fraction.
# EIP-4844, EIP-7691, EIP-8134 and EIP-8135 give them, each in its "Parameters" section.
#
# Repository: ethereum/EIPs
# Commit: b055feec322fbc37e9d77a393a50b3ff56b31c92
FORK_SCHEDULES = {
    "cancun": (3, 6, 3_338_477),
    "prague": (6, 9, 5_007_716),
    "bpo1": (10, 15, 8_346_193),
    "bpo2": (14, 21, 11_684_671),
}

# Paris activates at the child of the last proof-of-work block, as EIP-3675 sets.
PARIS_BLOCK = 1_450_409
# A block well after Paris, for the forks by time.
LATER_BLOCK = 2_000_000


def terminal_block_hash() -> bytes:
    """The hash of the last proof-of-work block, as the consensus configuration gives it."""
    match = re.search(r"^TERMINAL_BLOCK_HASH: 0x([0-9a-f]{64})$", CONFIG, re.MULTILINE)
    assert match is not None
    return bytes.fromhex(match.group(1))


def genesis_hash() -> bytes:
    """The hash of the genesis block that the genesis file describes, at London."""
    state = rlp.encode(
        [
            [
                bytes.fromhex(address[2:]),
                b"",
                int(account["balance"], 16).to_bytes(32, "big").lstrip(b"\0"),
                b"",
                [],
            ]
            for address, account in GENESIS["alloc"].items()
        ]
    )
    block = blocks.genesis_block(
        "london",
        state,
        coinbase=bytes.fromhex(GENESIS["coinbase"][2:]),
        difficulty=int(GENESIS["difficulty"], 16),
        gas_limit=int(GENESIS["gasLimit"], 16),
        timestamp=int(GENESIS["timestamp"], 16),
        extra_data=bytes.fromhex(GENESIS["extraData"][2:]),
        mix_hash=bytes.fromhex(GENESIS["mixhash"][2:]),
        nonce=int(GENESIS["nonce"], 16).to_bytes(8, "big"),
    )
    return keccak256(rlp.encode(rlp.decode(block)[0]))


def test_genesis_file_agrees_with_the_eips() -> None:
    config = GENESIS["config"]
    assert config["chainId"] == 11_155_111
    assert all(config[key] == 0 for key, _ in GENESIS_BLOCKS)
    assert [config[key] for _, _, _, key in TIMES] == [time for time, _, _, _ in TIMES]


def test_configuration_is_the_genesis_file() -> None:
    """Every value of the configuration comes from the genesis file, but Paris from the header."""
    config = GENESIS["config"]
    number = int.from_bytes(rlp.decode(TERMINAL_HEADER)[8], "big")
    blocks_by_fork = {fork: config[key] for key, fork in GENESIS_BLOCKS}
    expected = (
        [["frontier", "block", 0]]
        + [[fork, "block", block] for fork, block in blocks_by_fork.items()]
        + [["paris", "block", number + 1]]
        + [[fork, "time", config[key]] for _, _, fork, key in TIMES]
    )
    sepolia = chain_config("sepolia")
    assert sepolia["chainId"] == config["chainId"]
    assert sepolia["depositContractAddress"] == config["depositContractAddress"].lower()
    assert sepolia["activations"] == expected
    assert sepolia["blobSchedules"] == []


def test_blob_schedules_are_those_of_the_forks() -> None:
    """Each schedule of the genesis file is the one of its fork's EIP, so none is Sepolia's own."""
    schedules = GENESIS["config"]["blobSchedule"]
    assert {
        fork: (s["target"], s["max"], s["baseFeeUpdateFraction"]) for fork, s in schedules.items()
    } == FORK_SCHEDULES


# Each named chain, and blocks on both sides of its boundaries.
CHAINS = [
    ("mainnet", [15_537_393, 15_537_394, 20_000_000]),
    ("hoodi", [0, 1]),
    ("sepolia", [0, PARIS_BLOCK - 1, PARIS_BLOCK, LATER_BLOCK]),
]
# Timestamps on both sides of each fork by time of the three chains.
BOUNDARY_TIMES = sorted(
    {0, 1_681_338_455, 1_710_338_135, 1_746_612_311, 1_764_798_551, 1_765_290_071}
    | {1_767_747_671, 1_742_999_832, 1_761_677_592, 1_762_365_720, 1_762_955_544}
    | {time for time, _, _, _ in TIMES}
)


@pytest.mark.parametrize("name, numbers", CHAINS)
def test_configuration_reads_back(name, numbers) -> None:
    """The configuration as a `dict` gives the forks of the chain, and a file holds it whole."""
    config = chain_config(name)
    for number in numbers:
        for time in BOUNDARY_TIMES:
            for timestamp in (time - 1, time) if time else (0,):
                expected = active_fork(name, number, timestamp)
                assert active_fork(config, number, timestamp) == expected
    write_execution_config(config)


def test_unknown_chain() -> None:
    with raises(ChainError, "no chain is named goerli") as error:
        chain_config("goerli")
    assert error.value.code == 0
    with raises(ChainError, "no chain is named goerli") as error:
        active_fork("goerli", 0, 0)
    assert error.value.code == 0


def test_genesis_is_london() -> None:
    assert active_fork("sepolia", 0, int(GENESIS["timestamp"], 16)) == "london"
    assert active_fork("sepolia", 0, 0) == "london"


def test_terminal_header_is_the_published_one() -> None:
    """The header hashes to the published terminal block hash, so its number is authentic."""
    assert keccak256(TERMINAL_HEADER) == terminal_block_hash()
    fields = rlp.decode(TERMINAL_HEADER)
    assert int.from_bytes(fields[8], "big") + 1 == PARIS_BLOCK


def test_paris_boundary() -> None:
    fields = rlp.decode(TERMINAL_HEADER)
    number = int.from_bytes(fields[8], "big")
    timestamp = int.from_bytes(fields[11], "big")
    # The last proof-of-work block is at London, and its child at Paris.
    assert active_fork("sepolia", number, timestamp) == "london"
    assert active_fork("sepolia", number + 1, timestamp + 1) == "paris"
    # The merge netsplit block of the genesis file is no activation.
    netsplit = GENESIS["config"]["mergeNetsplitBlock"]
    assert active_fork("sepolia", netsplit - 1, timestamp) == "paris"
    assert active_fork("sepolia", netsplit, timestamp) == "paris"


@pytest.mark.parametrize("timestamp, before, fork, key", TIMES)
def test_time_boundary(timestamp: int, before: str, fork: str, key: str) -> None:
    assert active_fork("sepolia", LATER_BLOCK, timestamp - 1) == before
    assert active_fork("sepolia", LATER_BLOCK, timestamp) == fork


def test_glamsterdam_is_last() -> None:
    assert active_fork("sepolia", LATER_BLOCK, 2**64 - 1) == "glamsterdam"


def test_fork_ids() -> None:
    """The fork hashes of EIP-7607 follow from the genesis block that the genesis file builds."""
    forks = [
        (name, BLOCK, 0)
        for name in [
            "frontier",
            "homestead",
            "tangerineWhistle",
            "spuriousDragon",
            "byzantium",
            "constantinople",
            "petersburg",
            "istanbul",
            "berlin",
            "london",
        ]
    ] + [(fork, TIME, time) for time, _, fork, _ in TIMES]
    # Paris activates by total difficulty, so the merge netsplit block takes its place.
    chain = forkid.schedule(
        genesis_hash(),
        int(GENESIS["timestamp"], 16),
        forks,
        merge_fork_block=GENESIS["config"]["mergeNetsplitBlock"],
    )
    for index, (time, _, _, _) in enumerate(TIMES):
        fork_hash, fork_next = forkid.fork_id(chain, LATER_BLOCK, time)
        following = TIMES[index + 1][0] if index + 1 < len(TIMES) else 0
        assert fork_next == following
        if time in FORK_HASHES:
            assert fork_hash == FORK_HASHES[time]


def test_timestamp_out_of_range() -> None:
    """A timestamp of 2^64 is not a 64-bit number, so it fails with code 0."""
    with raises(ChainError, f"expected an int below {2**64}, got {2**64}") as error:
        active_fork("sepolia", 0, 2**64)
    assert error.value.code == 0
