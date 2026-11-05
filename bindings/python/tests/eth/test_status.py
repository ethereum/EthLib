"""Status and BlockRangeUpdate of the eth capability, against hand-built messages.

The forms come from "Status (0x00)" and "BlockRangeUpdate (0x11)" of caps/eth.md in
ethereum/devp2p at the pin, and from EIP-7642 "Status message changes".
No official vectors exist, so each message is built here as RLP.
"""

import pytest

from ethlib.execution.network import BLOCK_RANGE_UPDATE, STATUS, EthWireError
from ethlib.execution.network import check_status, decode_message
from ethlib.networking import forkid
from ethlib.networking.forkid import BLOCK
from ethlib.serialization import rlp

GENESIS = bytes.fromhex("d4e56740f876aef8c010b86a40d5f56745a118d0906a34e69aec8c0db1cb8fa3")
LATEST_HASH = bytes(range(32))

# The chain of EIP-2124 "Test Cases": mainnet up to Petersburg.
SCHEDULE = forkid.schedule(GENESIS, 0, [
    ("frontier", BLOCK, 0),
    ("homestead", BLOCK, 1_150_000),
    ("daoFork", BLOCK, 1_920_000),
    ("tangerineWhistle", BLOCK, 2_463_000),
    ("spuriousDragon", BLOCK, 2_675_000),
    ("byzantium", BLOCK, 4_370_000),
    ("petersburg", BLOCK, 7_280_000),
])
HEAD = 7_987_396
# The identifier of that chain at HEAD, from EIP-2124 "Test Cases".
FORK_ID = [bytes.fromhex("668db0af"), b""]


def _p(n: int) -> bytes:
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def _status68(version: int = 68, fork_id: list = FORK_ID) -> bytes:
    td = 17_179_869_184
    return rlp.encode([_p(version), _p(1), _p(td), LATEST_HASH, GENESIS, fork_id])


def _status69(version: int = 69, fork_id: list = FORK_ID, earliest: int = 0,
              latest: int = HEAD) -> bytes:
    return rlp.encode([
        _p(version), _p(1), GENESIS, fork_id, _p(earliest), _p(latest), LATEST_HASH,
    ])


def test_status68_round_trip() -> None:
    assert decode_message(68, STATUS, _status68()) == _status68()


@pytest.mark.parametrize("version", [69, 70, 71, 72])
def test_status69_round_trip(version: int) -> None:
    data = _status69(version)
    assert decode_message(version, STATUS, data) == data


def test_eth68_rejects_status69() -> None:
    with pytest.raises(EthWireError) as info:
        decode_message(68, STATUS, _status69(68))
    assert info.value.code == 2


@pytest.mark.parametrize("version", [69, 70, 71, 72])
def test_later_versions_reject_status68(version: int) -> None:
    with pytest.raises(EthWireError) as info:
        decode_message(version, STATUS, _status68(version))
    assert info.value.code == 2


def test_block_range_update() -> None:
    data = rlp.encode([b"", _p(HEAD), LATEST_HASH])
    assert decode_message(69, BLOCK_RANGE_UPDATE, data) == data
    # eth/68 does not use the ID 0x11.
    with pytest.raises(EthWireError) as info:
        decode_message(68, BLOCK_RANGE_UPDATE, data)
    assert info.value.code == 1


@pytest.mark.parametrize(
    "data",
    [
        rlp.encode([b"", _p(HEAD)]),  # two fields
        rlp.encode([b"\x00", _p(HEAD), LATEST_HASH]),  # a scalar with a leading zero byte
        rlp.encode([b"", _p(HEAD), LATEST_HASH[:31]]),  # a hash of 31 bytes
    ],
)
def test_malformed_block_range_update(data: bytes) -> None:
    with pytest.raises(EthWireError) as info:
        decode_message(69, BLOCK_RANGE_UPDATE, data)
    assert info.value.code == 2


def test_unknown_message_id() -> None:
    with pytest.raises(EthWireError) as info:
        decode_message(69, 0x16, rlp.encode([]))
    assert info.value.code == 1


def test_unknown_version() -> None:
    with pytest.raises(EthWireError) as info:
        decode_message(67, STATUS, _status68(67))
    assert info.value.code == 0


@pytest.mark.parametrize("version, data", [(68, _status68()), (69, _status69()),
                                           (72, _status69(72))])
def test_status_accepted(version: int, data: bytes) -> None:
    check_status(version, SCHEDULE, HEAD, 0, data)


@pytest.mark.parametrize(
    "version, data, code",
    [
        # The Status announces another version than the negotiated one.
        (69, _status69(70), 101),
        (68, _status68(67), 101),
        # A remote of Rinkeby at Petersburg: incompatible, EIP-2124 "Test Cases".
        (69, _status69(fork_id=[bytes.fromhex("afec6b27"), b""]), 102),
        # The range starts after its end.
        (69, _status69(earliest=HEAD + 1), 103),
        # The Status of eth/69 on eth/68.
        (68, _status69(68), 2),
    ],
)
def test_status_refused(version: int, data: bytes, code: int) -> None:
    with pytest.raises(EthWireError) as info:
        check_status(version, SCHEDULE, HEAD, 0, data)
    assert info.value.code == code
