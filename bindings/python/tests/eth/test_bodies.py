"""The check of a BlockBodies answer against its header."""

from pathlib import Path

import pytest

import archives
from blocks.test_blocks import BEFORE_SHANGHAI, CASES, EMPTY_TRIE_ROOT, FORK_OF_NETWORK, _case_id
from ethlib.cryptography import keccak
from ethlib.execution.history import decode_era1
from ethlib.execution.network import EthWireError, check_body
from ethlib.serialization import rlp
from raising import raises
from trie_reference import Trie

# The rules come from "Block Encoding and Validity" in caps/eth.md of ethereum/devp2p at the pin.
# The accepted bodies are the blocks of tests/execution/blocks/blockchain_tests.json.
# The blocks of era 0 of mainnet are accepted too, and tests/sources.toml pins their archive.
# So is block 19426587 of mainnet, after Shapella, which portal_block_data holds.
# The refused ones are RLP built here.

ARCHIVE = "era1/mainnet-00000-5ec1ffb8"

# The Keccak-256 hash of the encoding of no ommers, 0xc0.
EMPTY_OMMERS_HASH = bytes.fromhex(
    "1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"
)


def _p(n: int) -> bytes:
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def _header(
    number: int = 100,
    ommers_hash: bytes = EMPTY_OMMERS_HASH,
    transactions_root: bytes = EMPTY_TRIE_ROOT,
    withdrawals_root: bytes | None = None,
) -> bytes:
    """A header of the fifteen fields of Frontier, plus a base fee and withdrawals root if given."""
    fields = [
        bytes(32),
        ommers_hash,
        bytes(20),
        bytes(32),
        transactions_root,
        bytes(32),
        bytes(256),
        _p(131072),
        _p(number),
        _p(5000),
        b"",
        _p(number),
        b"",
        bytes(32),
        bytes(8),
    ]
    if withdrawals_root is not None:
        # The base fee of London, then the withdrawals root of Shapella.
        fields += [_p(7), withdrawals_root]
    return rlp.encode(fields)


def _split(block: bytes) -> tuple[bytes, bytes]:
    """The header and the body of a block: its first item, and the list of the others."""
    items = rlp.decode(block)
    return rlp.encode(items[0]), rlp.encode(items[1:])


@pytest.mark.parametrize("case", CASES, ids=[_case_id(c) for c in CASES])
def test_fixture_body_accepted(case) -> None:
    header, body = _split(bytes.fromhex(case["rlp"]))
    check_body(FORK_OF_NETWORK[case["network"]], header, body)


def test_fixture_bodies_cover_both_shapes() -> None:
    # The fixtures hold bodies of both lengths: two items before Shapella, three from Shapella.
    lengths = {
        (case["network"] in BEFORE_SHANGHAI, len(rlp.decode(_split(bytes.fromhex(case["rlp"]))[1])))
        for case in CASES
    }
    assert lengths == {(True, 2), (False, 3)}


@pytest.mark.archive(ARCHIVE)
def test_mainnet_era_0_bodies_accepted() -> None:
    era1 = decode_era1(archives.download(ARCHIVE).read_bytes())
    for block in era1.blocks:
        check_body("frontier", block.header, block.body)
    # Some blocks of the era hold ommers, so the ommers hash is checked against real ones.
    assert any(rlp.decode(block.body)[1] != [] for block in era1.blocks)


def test_empty_body_accepted() -> None:
    check_body("frontier", _header(), rlp.encode([[], []]))
    check_body(
        "shapella",
        _header(withdrawals_root=EMPTY_TRIE_ROOT),
        rlp.encode([[], [], []]),
    )


# A legacy transaction as an empty list, which has the bytes 0xc0, and so a nonempty value.
TRANSACTION = []
WITHDRAWAL = [b"\x01", b"\x02", bytes(20), b"\x03"]

# The roots of the trie of one transaction or one withdrawal, at the key of the index 0.
TRANSACTIONS_ROOT = Trie({rlp.encode(b""): rlp.encode(TRANSACTION)}).root
WITHDRAWALS_ROOT = Trie({rlp.encode(b""): rlp.encode(WITHDRAWAL)}).root

# An ommer with a number after that of the header, and the header that commits to it.
LATE_OMMER = rlp.decode(_header(number=101))
LATE_HEADER = _header(ommers_hash=keccak.keccak256(rlp.encode([LATE_OMMER])))


@pytest.mark.parametrize(
    "fork, header, body, code, message",
    [
        pytest.param(
            "frontier",
            _header(),
            rlp.encode(b"\x01"),
            601,
            "body is not the RLP list of its parts: EthLib.Serialization.Rlp.RlpError.bytesAsList",
            id="decoding-not-a-list",
        ),
        pytest.param(
            "frontier",
            _header(),
            rlp.encode([[], [], [], []]),
            601,
            "body is not the RLP list of its parts: "
            "EthLib.Serialization.Rlp.RlpError.wrongFieldCount 2 4",
            id="decoding-before-shapella-four-items",
        ),
        pytest.param(
            "shapella",
            _header(withdrawals_root=EMPTY_TRIE_ROOT),
            rlp.encode([[], [], [], []]),
            601,
            "body is not the RLP list of its parts: "
            "EthLib.Serialization.Rlp.RlpError.wrongFieldCount 3 4",
            id="decoding-from-shapella-four-items",
        ),
        pytest.param(
            "frontier",
            _header(),
            rlp.encode([[b""], []]),
            610,
            "a transaction is an empty byte string",
            id="untyped-transaction-empty",
        ),
        pytest.param(
            "frontier",
            _header(),
            # A legacy transaction, the empty list 0xc0, sent as a byte string.
            rlp.encode([[rlp.encode(TRANSACTION)], []]),
            610,
            "a transaction is a byte string that starts with 0xc0, not a type",
            id="untyped-transaction-legacy-as-bytes",
        ),
        pytest.param(
            "frontier",
            _header(),
            rlp.encode([[b"\x80\x01"], []]),
            610,
            "a transaction is a byte string that starts with 0x80, not a type",
            id="untyped-transaction-first-byte-0x80",
        ),
        pytest.param(
            "frontier",
            _header(),
            rlp.encode([[TRANSACTION], []]),
            603,
            f"transactions have the root 0x{TRANSACTIONS_ROOT.hex()}, "
            f"not the transactions root 0x{EMPTY_TRIE_ROOT.hex()}",
            id="wrong-transactions-root",
        ),
        pytest.param(
            "shapella",
            _header(withdrawals_root=EMPTY_TRIE_ROOT),
            rlp.encode([[], []]),
            604,
            "body has no withdrawals, which the fork asks for",
            id="missing-withdrawals",
        ),
        pytest.param(
            "frontier",
            _header(),
            rlp.encode([[], [], []]),
            605,
            "body has withdrawals, which the fork does not have",
            id="unexpected-withdrawals",
        ),
        pytest.param(
            "shapella",
            _header(withdrawals_root=EMPTY_TRIE_ROOT),
            rlp.encode([[], [], [WITHDRAWAL]]),
            606,
            f"withdrawals have the root 0x{WITHDRAWALS_ROOT.hex()}, "
            f"not the withdrawals root 0x{EMPTY_TRIE_ROOT.hex()}",
            id="wrong-withdrawals-root",
        ),
        pytest.param(
            "frontier",
            _header(),
            rlp.encode([[], [[], [], []]]),
            607,
            "body holds 3 ommers, more than 2",
            id="too-many-ommers",
        ),
        pytest.param(
            "frontier",
            _header(),
            rlp.encode([[], [[]]]),
            608,
            f"ommers have the hash 0x{keccak.keccak256(rlp.encode([[]])).hex()}, "
            f"not the ommers hash 0x{EMPTY_OMMERS_HASH.hex()}",
            id="wrong-ommers-hash",
        ),
        pytest.param(
            "frontier",
            LATE_HEADER,
            rlp.encode([[], [LATE_OMMER]]),
            609,
            "ommer 0 has number 101, after the block",
            id="ommer-after-block",
        ),
    ],
)
def test_body_refused(fork: str, header: bytes, body: bytes, code: int, message: str) -> None:
    with raises(EthWireError, message) as info:
        check_body(fork, header, body)
    assert info.value.code == code


def test_ommer_at_the_block_passes() -> None:
    # The ommer has the number of the block, which the rule allows.
    ommer = rlp.decode(_header(number=100))
    header = _header(ommers_hash=keccak.keccak256(rlp.encode([ommer])))
    check_body("frontier", header, rlp.encode([[], [ommer]]))


def test_two_ommers_pass() -> None:
    # Two ommers is the most that the rule allows.
    ommers = [rlp.decode(_header(number=99)), rlp.decode(_header(number=100))]
    header = _header(ommers_hash=keccak.keccak256(rlp.encode(ommers)))
    check_body("frontier", header, rlp.encode([[], ommers]))


def test_header_that_does_not_decode_is_refused() -> None:
    # A Frontier header has fifteen fields, and Shapella asks for seventeen.
    message = (
        "header does not decode at this fork: "
        "EthLib.Serialization.Rlp.RlpError.wrongFieldCount 17 15"
    )
    with raises(EthWireError, message) as info:
        check_body("shapella", _header(), rlp.encode([[], [], []]))
    assert info.value.code == 0


def test_body_that_is_not_rlp_is_refused() -> None:
    with raises(EthWireError, "body is not RLP") as info:
        check_body("frontier", _header(), b"\xc1")
    assert info.value.code == 0


def test_fork_that_is_not_a_string_is_refused() -> None:
    with raises(TypeError, "fork must be str"):
        check_body(b"frontier", _header(), rlp.encode([[], []]))  # ty: ignore[invalid-argument-type]


# Block 19426587 of mainnet, the first block of Cancun, with its header and body as RLP.
# The file comes from ethereum/portal-spec-tests, and portal_block_data/README.md gives its pin.
MAINNET_BLOCK = Path(__file__).parent / "portal_block_data" / "block-data-19426587.yaml"

# The activation time of Cancun on mainnet, from the table of EIP-7569.
CANCUN_MAINNET_TIMESTAMP = 1710338135


def _mainnet_block() -> tuple[bytes, bytes]:
    """The header and the body of the pinned mainnet block."""
    fields = dict(line.split(": 0x") for line in MAINNET_BLOCK.read_text().splitlines())
    return bytes.fromhex(fields["header"]), bytes.fromhex(fields["body"])


def _root(entries: list[bytes]) -> bytes:
    """The root of the trie that maps the RLP of each index to its entry."""
    return Trie({rlp.encode(_p(i)): entry for i, entry in enumerate(entries)}).root


def test_mainnet_cancun_body_accepted() -> None:
    header, body = _mainnet_block()
    fields = rlp.decode(header)
    # The header is that of block 19426587, at the first timestamp of Cancun.
    assert int.from_bytes(fields[8], "big") == 19426587
    assert int.from_bytes(fields[11], "big") == CANCUN_MAINNET_TIMESTAMP
    transactions, ommers, withdrawals = rlp.decode(body)
    # The block has transactions and withdrawals, and no ommers, as every block after the Merge.
    assert (len(transactions), len(ommers), len(withdrawals)) == (37, 0, 16)
    # The reference trie gives the roots of the header, so the test does not trust the check alone.
    entries = [rlp.encode(item) if isinstance(item, list) else item for item in transactions]
    assert _root(entries) == fields[4]
    assert _root([rlp.encode(withdrawal) for withdrawal in withdrawals]) == fields[16]
    assert keccak.keccak256(rlp.encode(ommers)) == fields[1]
    check_body("dencun", header, body)


def test_mainnet_cancun_body_without_its_last_transaction_is_refused() -> None:
    header, body = _mainnet_block()
    transactions, ommers, withdrawals = rlp.decode(body)
    kept = transactions[:-1]
    entries = [rlp.encode(item) if isinstance(item, list) else item for item in kept]
    message = (
        f"transactions have the root 0x{_root(entries).hex()}, "
        f"not the transactions root 0x{rlp.decode(header)[4].hex()}"
    )
    with raises(EthWireError, message) as info:
        check_body("dencun", header, rlp.encode([kept, ommers, withdrawals]))
    assert info.value.code == 603


def test_mainnet_cancun_body_without_its_last_withdrawal_is_refused() -> None:
    header, body = _mainnet_block()
    transactions, ommers, withdrawals = rlp.decode(body)
    kept = withdrawals[:-1]
    message = (
        f"withdrawals have the root 0x{_root([rlp.encode(w) for w in kept]).hex()}, "
        f"not the withdrawals root 0x{rlp.decode(header)[16].hex()}"
    )
    with raises(EthWireError, message) as info:
        check_body("dencun", header, rlp.encode([transactions, ommers, kept]))
    assert info.value.code == 606


def test_mainnet_cancun_body_with_an_ommer_is_refused() -> None:
    # The block's own header as an ommer: its number is not after the block, so the hash refuses it.
    header, body = _mainnet_block()
    transactions, _, withdrawals = rlp.decode(body)
    ommers = [rlp.decode(header)]
    message = (
        f"ommers have the hash 0x{keccak.keccak256(rlp.encode(ommers)).hex()}, "
        f"not the ommers hash 0x{EMPTY_OMMERS_HASH.hex()}"
    )
    with raises(EthWireError, message) as info:
        check_body("dencun", header, rlp.encode([transactions, ommers, withdrawals]))
    assert info.value.code == 608
