"""The fork identifier against the test cases of EIP-2124, EIP-6122 and EIP-7910."""

import pytest

from ethlib.networking import forkid
from ethlib.networking.forkid import BLOCK, TIME, ForkIdError
from raising import raises

# The test cases of EIP-2124 and EIP-6122.
#
# Section: Test Cases
# Files: EIPS/eip-2124.md, EIPS/eip-6122.md
# Repository: ethereum/EIPs
# Commit: 46976b2a9bf99f727fb87dc8c809e3a3cdc6b445
# Licence: CC0-1.0
#
# Each genesis hash is checked by the first fork hash of its chain, the CRC-32 of the hash alone.
# EIP-1898 "Specification" gives the genesis hash of mainnet.
MAINNET_GENESIS = bytes.fromhex("d4e56740f876aef8c010b86a40d5f56745a118d0906a34e69aec8c0db1cb8fa3")
ROPSTEN_GENESIS = bytes.fromhex("41941023680923e0fe4d74a34bdac8141f2540e3ae90623718e47d66d1ca4a2d")
RINKEBY_GENESIS = bytes.fromhex("6341fd3daf94b748c72ced5a5b26028f2474f5f00d824504e4fa37a75767e177")
GOERLI_GENESIS = bytes.fromhex("bf7e331f7f7c1dd2e05159666b3bf8bc7a8a3a9eb1d518969eab529dd9b88c1a")

MAX_UINT64 = 2**64 - 1

# The chains of EIP-2124 "Test Cases", with the forks up to Petersburg or Istanbul.
MAINNET_FORKS = [
    ("frontier", BLOCK, 0),
    ("homestead", BLOCK, 1_150_000),
    ("daoFork", BLOCK, 1_920_000),
    ("tangerineWhistle", BLOCK, 2_463_000),
    ("spuriousDragon", BLOCK, 2_675_000),
    ("byzantium", BLOCK, 4_370_000),
    ("constantinople", BLOCK, 7_280_000),
    ("petersburg", BLOCK, 7_280_000),
]
MAINNET = forkid.schedule(MAINNET_GENESIS, 0, MAINNET_FORKS)
ROPSTEN = forkid.schedule(
    ROPSTEN_GENESIS,
    0,
    [
        ("frontier", BLOCK, 0),
        ("homestead", BLOCK, 0),
        ("tangerineWhistle", BLOCK, 0),
        ("spuriousDragon", BLOCK, 10),
        ("byzantium", BLOCK, 1_700_000),
        ("constantinople", BLOCK, 4_230_000),
        ("petersburg", BLOCK, 4_939_394),
        ("istanbul", BLOCK, 6_485_846),
    ],
)
RINKEBY = forkid.schedule(
    RINKEBY_GENESIS,
    0,
    [
        ("frontier", BLOCK, 0),
        ("homestead", BLOCK, 1),
        ("tangerineWhistle", BLOCK, 2),
        ("spuriousDragon", BLOCK, 3),
        ("byzantium", BLOCK, 1_035_301),
        ("constantinople", BLOCK, 3_660_663),
        ("petersburg", BLOCK, 4_321_234),
        ("istanbul", BLOCK, 5_435_345),
    ],
)
GOERLI = forkid.schedule(
    GOERLI_GENESIS,
    0,
    [
        ("frontier", BLOCK, 0),
        ("homestead", BLOCK, 0),
        ("tangerineWhistle", BLOCK, 0),
        ("spuriousDragon", BLOCK, 0),
        ("byzantium", BLOCK, 0),
        ("constantinople", BLOCK, 0),
        ("petersburg", BLOCK, 0),
        ("istanbul", BLOCK, 1_561_651),
    ],
)

# The chain of EIP-6122 "Test Cases": mainnet to Gray Glacier.
# Then a merge netsplit block at 18000000, and withdrawals at time 1668000000.
# Paris activates by total difficulty, so its block is not a fork of the identifier.
# The netsplit block is the FORK_NEXT_VALUE of EIP-3675.
WITHDRAWALS = forkid.schedule(
    MAINNET_GENESIS,
    0,
    MAINNET_FORKS
    + [
        ("istanbul", BLOCK, 9_069_000),
        ("muirGlacier", BLOCK, 9_200_000),
        ("berlin", BLOCK, 12_244_000),
        ("london", BLOCK, 12_965_000),
        ("arrowGlacier", BLOCK, 13_773_000),
        ("grayGlacier", BLOCK, 15_050_000),
        ("paris", BLOCK, 15_537_394),
        ("shapella", TIME, 1_668_000_000),
    ],
    merge_fork_block=18_000_000,
)

# (chain, head number, head timestamp, fork hash, next fork).
IDS = [
    # EIP-2124, mainnet.
    (MAINNET, 0, 0, 0xFC64EC04, 1150000),
    (MAINNET, 1149999, 0, 0xFC64EC04, 1150000),
    (MAINNET, 1150000, 0, 0x97C2C34C, 1920000),
    (MAINNET, 1919999, 0, 0x97C2C34C, 1920000),
    (MAINNET, 1920000, 0, 0x91D1F948, 2463000),
    (MAINNET, 2462999, 0, 0x91D1F948, 2463000),
    (MAINNET, 2463000, 0, 0x7A64DA13, 2675000),
    (MAINNET, 2674999, 0, 0x7A64DA13, 2675000),
    (MAINNET, 2675000, 0, 0x3EDD5B10, 4370000),
    (MAINNET, 4369999, 0, 0x3EDD5B10, 4370000),
    (MAINNET, 4370000, 0, 0xA00BC324, 7280000),
    (MAINNET, 7279999, 0, 0xA00BC324, 7280000),
    (MAINNET, 7280000, 0, 0x668DB0AF, 0),
    (MAINNET, 7987396, 0, 0x668DB0AF, 0),
    # EIP-2124, Ropsten.
    (ROPSTEN, 0, 0, 0x30C7DDBC, 10),
    (ROPSTEN, 9, 0, 0x30C7DDBC, 10),
    (ROPSTEN, 10, 0, 0x63760190, 1700000),
    (ROPSTEN, 1699999, 0, 0x63760190, 1700000),
    (ROPSTEN, 1700000, 0, 0x3EA159C7, 4230000),
    (ROPSTEN, 4229999, 0, 0x3EA159C7, 4230000),
    (ROPSTEN, 4230000, 0, 0x97B544F3, 4939394),
    (ROPSTEN, 4939393, 0, 0x97B544F3, 4939394),
    (ROPSTEN, 4939394, 0, 0xD6E2149B, 6485846),
    (ROPSTEN, 6485845, 0, 0xD6E2149B, 6485846),
    (ROPSTEN, 6485846, 0, 0x4BC66396, 0),
    (ROPSTEN, 7500000, 0, 0x4BC66396, 0),
    # EIP-2124, Rinkeby.
    (RINKEBY, 0, 0, 0x3B8E0691, 1),
    (RINKEBY, 1, 0, 0x60949295, 2),
    (RINKEBY, 2, 0, 0x8BDE40DD, 3),
    (RINKEBY, 3, 0, 0xCB3A64BB, 1035301),
    (RINKEBY, 1035300, 0, 0xCB3A64BB, 1035301),
    (RINKEBY, 1035301, 0, 0x8D748B57, 3660663),
    (RINKEBY, 3660662, 0, 0x8D748B57, 3660663),
    (RINKEBY, 3660663, 0, 0xE49CAB14, 4321234),
    (RINKEBY, 4321233, 0, 0xE49CAB14, 4321234),
    (RINKEBY, 4321234, 0, 0xAFEC6B27, 5435345),
    (RINKEBY, 5435344, 0, 0xAFEC6B27, 5435345),
    (RINKEBY, 5435345, 0, 0xCBDB8838, 0),
    (RINKEBY, 6000000, 0, 0xCBDB8838, 0),
    # EIP-2124, Goerli.
    (GOERLI, 0, 0, 0xA3F5AB08, 1561651),
    (GOERLI, 1561650, 0, 0xA3F5AB08, 1561651),
    (GOERLI, 1561651, 0, 0xC25EFA5C, 0),
    (GOERLI, 2000000, 0, 0xC25EFA5C, 0),
    # EIP-6122, mainnet with withdrawals.
    (WITHDRAWALS, 0, 0, 0xFC64EC04, 1150000),
    (WITHDRAWALS, 1149999, 0, 0xFC64EC04, 1150000),
    (WITHDRAWALS, 1150000, 0, 0x97C2C34C, 1920000),
    (WITHDRAWALS, 1919999, 0, 0x97C2C34C, 1920000),
    (WITHDRAWALS, 1920000, 0, 0x91D1F948, 2463000),
    (WITHDRAWALS, 2462999, 0, 0x91D1F948, 2463000),
    (WITHDRAWALS, 2463000, 0, 0x7A64DA13, 2675000),
    (WITHDRAWALS, 2674999, 0, 0x7A64DA13, 2675000),
    (WITHDRAWALS, 2675000, 0, 0x3EDD5B10, 4370000),
    (WITHDRAWALS, 4369999, 0, 0x3EDD5B10, 4370000),
    (WITHDRAWALS, 4370000, 0, 0xA00BC324, 7280000),
    (WITHDRAWALS, 7279999, 0, 0xA00BC324, 7280000),
    (WITHDRAWALS, 7280000, 0, 0x668DB0AF, 9069000),
    (WITHDRAWALS, 9068999, 0, 0x668DB0AF, 9069000),
    (WITHDRAWALS, 9069000, 0, 0x879D6E30, 9200000),
    (WITHDRAWALS, 9199999, 0, 0x879D6E30, 9200000),
    (WITHDRAWALS, 9200000, 0, 0xE029E991, 12244000),
    (WITHDRAWALS, 12243999, 0, 0xE029E991, 12244000),
    (WITHDRAWALS, 12244000, 0, 0x0EB440F6, 12965000),
    (WITHDRAWALS, 12964999, 0, 0x0EB440F6, 12965000),
    (WITHDRAWALS, 12965000, 0, 0xB715077D, 13773000),
    (WITHDRAWALS, 13772999, 0, 0xB715077D, 13773000),
    (WITHDRAWALS, 13773000, 0, 0x20C327FC, 15050000),
    (WITHDRAWALS, 15049999, 0, 0x20C327FC, 15050000),
    (WITHDRAWALS, 15050000, 0, 0xF0AFD0E3, 18000000),
    (WITHDRAWALS, 18000000, 0, 0x4FB8A872, 1668000000),
    (WITHDRAWALS, 20000000, 0, 0x4FB8A872, 1668000000),
    (WITHDRAWALS, 20000000, 1668000000, 0xC1FDF181, 0),
    (WITHDRAWALS, 20100000, 2669000000, 0xC1FDF181, 0),
]


@pytest.mark.parametrize("chain, number, timestamp, fork_hash, fork_next", IDS)
def test_fork_id(chain: bytes, number: int, timestamp: int, fork_hash: int, fork_next: int) -> None:
    assert forkid.fork_id(chain, number, timestamp) == (fork_hash.to_bytes(4, "big"), fork_next)


def _id(fork_hash: int, fork_next: int) -> bytes:
    return forkid.encode(fork_hash.to_bytes(4, "big"), fork_next)


# The codes of the refusals: 1 is ErrRemoteStale, 2 is ErrLocalIncompatibleOrStale.
REMOTE_STALE = 1
LOCAL_INCOMPATIBLE_OR_STALE = 2
# The message of each refusal.
REFUSALS = {
    REMOTE_STALE: "remote is on an earlier fork and announces another next fork",
    LOCAL_INCOMPATIBLE_OR_STALE: "chains are incompatible, or the local node is stale",
}

# (chain, head number, head timestamp, remote hash, remote next, refusal code or None).
VALIDATIONS = [
    # EIP-2124, a mainnet node at most at Petersburg.
    (MAINNET, 7987396, 0, 0x668DB0AF, 0, None),
    (MAINNET, 7987396, 0, 0x668DB0AF, MAX_UINT64, None),
    (MAINNET, 7279999, 0, 0xA00BC324, 0, None),
    (MAINNET, 7279999, 0, 0xA00BC324, 7280000, None),
    (MAINNET, 7279999, 0, 0xA00BC324, MAX_UINT64, None),
    (MAINNET, 7987396, 0, 0xA00BC324, 7280000, None),
    (MAINNET, 7987396, 0, 0x3EDD5B10, 4370000, None),
    (MAINNET, 7279999, 0, 0x668DB0AF, 0, None),
    (MAINNET, 4369999, 0, 0xA00BC324, 0, None),
    (MAINNET, 7987396, 0, 0xA00BC324, 0, REMOTE_STALE),
    (MAINNET, 7987396, 0, 0x5CDDC0E1, 0, LOCAL_INCOMPATIBLE_OR_STALE),
    (MAINNET, 7279999, 0, 0x5CDDC0E1, 0, LOCAL_INCOMPATIBLE_OR_STALE),
    (MAINNET, 7987396, 0, 0xAFEC6B27, 0, LOCAL_INCOMPATIBLE_OR_STALE),
    (MAINNET, 88888888, 0, 0x668DB0AF, 88888888, LOCAL_INCOMPATIBLE_OR_STALE),
    (MAINNET, 7279999, 0, 0xA00BC324, 7279999, LOCAL_INCOMPATIBLE_OR_STALE),
    # EIP-6122, a mainnet node with withdrawals.
    (WITHDRAWALS, 20000000, 1668000001, 0xC1FDF181, 0, None),
    (WITHDRAWALS, 20000000, 1668000001, 0xC1FDF181, MAX_UINT64, None),
    (WITHDRAWALS, 7279999, 1667999999, 0xA00BC324, 0, None),
    (WITHDRAWALS, 7279999, 1667999999, 0xA00BC324, 7280000, None),
    (WITHDRAWALS, 7279999, 1667999999, 0xA00BC324, MAX_UINT64, None),
    (WITHDRAWALS, 20000000, 1668000000, 0xA00BC324, 7280000, None),
    (WITHDRAWALS, 20000000, 1668000001, 0xA00BC324, 7280000, None),
    (WITHDRAWALS, 20000000, 1668000001, 0x3EDD5B10, 4370000, None),
    (WITHDRAWALS, 7279999, 1667999999, 0x668DB0AF, 0, None),
    (WITHDRAWALS, 4369999, 1667999999, 0xA00BC324, 0, None),
    (WITHDRAWALS, 20000000, 1668000001, 0xA00BC324, 0, REMOTE_STALE),
    (WITHDRAWALS, 20000000, 1668000001, 0x5CDDC0E1, 0, LOCAL_INCOMPATIBLE_OR_STALE),
    (WITHDRAWALS, 20000000, 1668000001, 0xAFEC6B27, 0, LOCAL_INCOMPATIBLE_OR_STALE),
    (WITHDRAWALS, 88888888, 1668000001, 0xF0AFD0E3, 88888888, REMOTE_STALE),
    (WITHDRAWALS, 20000000, 1668000001, 0xA00BC324, 7279999, REMOTE_STALE),
]


@pytest.mark.parametrize("chain, number, timestamp, fork_hash, fork_next, code", VALIDATIONS)
def test_validate(
    chain: bytes, number: int, timestamp: int, fork_hash: int, fork_next: int, code: int | None
) -> None:
    remote = _id(fork_hash, fork_next)
    if code is None:
        forkid.validate(chain, number, timestamp, remote)
    else:
        with raises(ForkIdError, REFUSALS[code]) as info:
            forkid.validate(chain, number, timestamp, remote)
        assert info.value.code == code


# The RLP encodings of EIP-2124 "Test Cases".
ENCODINGS = [
    (0, 0, "c6840000000080"),
    (0xDEADBEEF, 0xBADDCAFE, "ca84deadbeef84baddcafe"),
    (0xFFFFFFFF, MAX_UINT64, "ce84ffffffff88ffffffffffffffff"),
]


@pytest.mark.parametrize("fork_hash, fork_next, encoding", ENCODINGS)
def test_encoding(fork_hash: int, fork_next: int, encoding: str) -> None:
    assert _id(fork_hash, fork_next).hex() == encoding
    # The node reads the identifier, and refuses it as a hash of another chain.
    with raises(ForkIdError, "chains are incompatible, or the local node is stale") as info:
        forkid.validate(MAINNET, 0, 0, bytes.fromhex(encoding))
    assert info.value.code == LOCAL_INCOMPATIBLE_OR_STALE


def test_mainnet_identifier_bytes() -> None:
    # The identifier of a node of the chain of EIP-2124 at Petersburg, as the node encodes it.
    assert forkid.mainnet_fork_id(7987396, 0)[0] == bytes.fromhex("668db0af")


@pytest.mark.parametrize(
    "remote",
    [
        "c58400000000",  # one field
        "c58300000080",  # a hash of 3 bytes
        "c6840000000000",  # a next fork with a leading zero byte
        "cf840000000089010000000000000000",  # a next fork of 2^64
    ],
)
def test_malformed_identifier(remote: str) -> None:
    with raises(ForkIdError, "remote is not an RLP fork identifier") as info:
        forkid.validate(MAINNET, 0, 0, bytes.fromhex(remote))
    assert info.value.code == 0


# The fork IDs of Hoodi in EIP-7910 "Hoodi Cancun Config" and "Hoodi Prague Config".
#
# File: EIPS/eip-7910.md
# Repository: ethereum/EIPs
# Commit: 46976b2a9bf99f727fb87dc8c809e3a3cdc6b445
# Licence: CC0-1.0
#
# Hoodi starts with every fork up to Cancun at genesis, so none of them is a fork.
# Its genesis hash is checked by the Cancun fork ID, the CRC-32 of the hash alone.
HOODI_GENESIS = bytes.fromhex("bbe312868b376a3001692a646dd2d7d1e4406380dfd86b98aa8a34d1557c971b")
HOODI = forkid.schedule(
    HOODI_GENESIS,
    0,
    [
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
            "paris",
        ]
    ]
    + [
        ("shapella", TIME, 0),
        ("dencun", TIME, 0),
        ("pectra", TIME, 1_742_999_832),
    ],
)


def test_eip6122_example() -> None:
    # EIP-6122 "Specification": a fork at time 1668000000 right after Homestead.
    chain = forkid.schedule(
        MAINNET_GENESIS,
        0,
        [
            ("frontier", BLOCK, 0),
            ("homestead", BLOCK, 1_150_000),
            ("shapella", TIME, 1_668_000_000),
        ],
    )
    assert forkid.fork_id(chain, 1_150_000, 1_668_000_000) == (bytes.fromhex("cb37b2ee"), 0)


def test_hoodi() -> None:
    assert forkid.fork_id(HOODI, 0, 0) == (bytes.fromhex("bef71d30"), 1_742_999_832)
    assert forkid.fork_id(HOODI, 1, 1_742_999_832) == (bytes.fromhex("0929e24e"), 0)


# The boundaries of mainnet, from ChainConfig.mainnet, against the hashes above.
# EIP-6122 gives no mainnet hash after Gray Glacier, so these check only the fork order.
MAINNET_TIMES = [
    1_681_338_455,
    1_710_338_135,
    1_746_612_311,
    1_764_798_551,
    1_765_290_071,
    1_767_747_671,
]


def test_mainnet_blocks() -> None:
    # The hashes of mainnet agree with EIP-6122 up to Gray Glacier.
    for chain, number, timestamp, fork_hash, fork_next in IDS:
        if chain is WITHDRAWALS and number < 15_050_000:
            assert forkid.mainnet_fork_id(number, timestamp) == (
                fork_hash.to_bytes(4, "big"),
                fork_next,
            )
    # Mainnet sets no merge netsplit block, so Shapella follows Gray Glacier.
    assert forkid.mainnet_fork_id(15_050_000, 0) == (bytes.fromhex("f0afd0e3"), MAINNET_TIMES[0])
    assert forkid.mainnet_fork_id(20_000_000, MAINNET_TIMES[0] - 1)[1] == MAINNET_TIMES[0]


def test_mainnet_times() -> None:
    hashes = set()
    for index, timestamp in enumerate(MAINNET_TIMES):
        fork_hash, fork_next = forkid.mainnet_fork_id(20_000_000, timestamp)
        hashes.add(fork_hash)
        following = MAINNET_TIMES[index + 1] if index + 1 < len(MAINNET_TIMES) else 0
        assert fork_next == following
        # The fork before announces this one as its next fork.
        assert forkid.mainnet_fork_id(20_000_000, timestamp - 1)[1] == timestamp
    # Each fork by time changes the hash.
    assert len(hashes) == len(MAINNET_TIMES)
