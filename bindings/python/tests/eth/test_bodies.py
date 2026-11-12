"""The check of a BlockBodies answer against its header."""

import pytest

import archives
from blocks.test_blocks import BEFORE_SHANGHAI, CASES, EMPTY_TRIE_ROOT, FORK_OF_NETWORK, _case_id
from ethlib.cryptography import keccak
from ethlib.execution.history import decode_era1
from ethlib.execution.network import EthWireError, check_body
from ethlib.serialization import rlp
from raising import raises

# The rules come from "Block Encoding and Validity" in caps/eth.md of ethereum/devp2p at the pin.
# The accepted bodies are the blocks of tests/execution/blocks/blockchain_tests.json.
# The blocks of era 0 of mainnet are accepted too, and tests/sources.toml pins their archive.
# The refused ones are RLP built here.

ARCHIVE = "era1/mainnet-00000-5ec1ffb8"

# The Keccak-256 hash of the encoding of no ommers, 0xc0.
EMPTY_OMMERS_HASH = bytes.fromhex("1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347")


def _p(n: int) -> bytes:
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def _header(
    number: int = 100,
    ommers_hash: bytes = EMPTY_OMMERS_HASH,
    transactions_root: bytes = EMPTY_TRIE_ROOT,
    withdrawals_root: bytes | None = None,
) -> bytes:
    """A header of the fifteen fields of Frontier, with the base fee and withdrawals root if given."""
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
            "a transaction is a byte string that does not start with a type",
            id="untyped-transaction-empty",
        ),
        pytest.param(
            "frontier",
            _header(),
            # A legacy transaction, the empty list 0xc0, sent as a byte string.
            rlp.encode([[rlp.encode(TRANSACTION)], []]),
            610,
            "a transaction is a byte string that does not start with a type",
            id="untyped-transaction-legacy-as-bytes",
        ),
        pytest.param(
            "frontier",
            _header(),
            rlp.encode([[b"\x80\x01"], []]),
            610,
            "a transaction is a byte string that does not start with a type",
            id="untyped-transaction-first-byte-0x80",
        ),
        pytest.param(
            "frontier",
            _header(),
            rlp.encode([[TRANSACTION], []]),
            603,
            "transactions do not have the transactions root of the header",
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
            "withdrawals do not have the withdrawals root of the header",
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
            "ommers do not have the ommers hash of the header",
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
