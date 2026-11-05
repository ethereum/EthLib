"""Headers and blocks against the blockchain tests of execution-specs."""

import json
from pathlib import Path

import pytest

from ethlib.execution import blocks
from ethlib.serialization import rlp

_REPO = Path(__file__).resolve().parents[4]
_CASES_FILE = _REPO / "tests" / "execution" / "blocks" / "blockchain_tests.json"
CASES = json.loads(_CASES_FILE.read_text())

# The network of a fixture, and the case of the Lean fork type that it names.
FORK_OF_NETWORK = {
    "Frontier": "frontier",
    "Homestead": "homestead",
    "TangerineWhistle": "tangerineWhistle",
    "SpuriousDragon": "spuriousDragon",
    "Byzantium": "byzantium",
    "ConstantinopleFix": "petersburg",
    "Istanbul": "istanbul",
    "Berlin": "berlin",
    "London": "london",
    "Paris": "paris",
    "Shanghai": "shapella",
    "Cancun": "dencun",
    "Prague": "pectra",
    "Osaka": "fusaka",
    "Amsterdam": "glamsterdam",
}

# The networks before London, whose headers have the 15 fields of Frontier.
BEFORE_LONDON = {"Frontier", "Homestead", "TangerineWhistle", "SpuriousDragon", "Byzantium",
                 "ConstantinopleFix", "Istanbul", "Berlin"}


def _first_item(data: bytes) -> bytes:
    """The encoding of the first item in the payload of the RLP list `data`."""
    # A block and its header are long lists, so both prefixes are in the long form.
    assert data[0] >= 0xF8
    start = 1 + data[0] - 0xF7
    head = data[start]
    assert head >= 0xF8
    length_bytes = head - 0xF7
    length = int.from_bytes(data[start + 1:start + 1 + length_bytes], "big")
    return data[start:start + 1 + length_bytes + length]


def _case_id(case) -> str:
    return f"{case['network']}-{case['test'].split('::')[-1][:60]}-{case['block']}"


@pytest.mark.parametrize("case", CASES, ids=[_case_id(c) for c in CASES])
def test_fixture_block(case) -> None:
    fork = FORK_OF_NETWORK[case["network"]]
    block = bytes.fromhex(case["rlp"])
    # The decoder accepts the block, and its encoding gives back the same bytes.
    assert blocks.reencode(fork, block) == block
    # The header hashes to the hash of the fixture.
    assert blocks.header_hash(fork, _first_item(block)) == bytes.fromhex(case["hash"])


@pytest.mark.parametrize("case", CASES, ids=[_case_id(c) for c in CASES])
def test_header_rejected_at_other_fork(case) -> None:
    # A London header has one more field than a Frontier header, so each fork rejects the other.
    other = "london" if case["network"] in BEFORE_LONDON else "frontier"
    header = _first_item(bytes.fromhex(case["rlp"]))
    with pytest.raises(ValueError):
        blocks.header_hash(other, header)


# The networks before Shanghai, whose blocks have no withdrawals.
BEFORE_SHANGHAI = BEFORE_LONDON | {"London", "Paris"}

# The empty trie has this root, the Keccak-256 hash of 0x80.
EMPTY_TRIE_ROOT = bytes.fromhex(
    "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")


@pytest.mark.parametrize("case", CASES, ids=[_case_id(c) for c in CASES])
def test_body_roots(case) -> None:
    fork = FORK_OF_NETWORK[case["network"]]
    block = bytes.fromhex(case["rlp"])
    header = rlp.decode(block)[0]
    # The roots of the body are the roots that the header of the fixture holds.
    assert blocks.transactions_root(fork, block) == header[4]
    if case["network"] in BEFORE_SHANGHAI:
        with pytest.raises(blocks.BlockError, match="before Shapella") as error:
            blocks.withdrawals_root(fork, block)
        assert error.value.code == 0
    else:
        assert blocks.withdrawals_root(fork, block) == header[16]


def test_body_roots_cover_both_cases() -> None:
    # The fixtures hold empty and nonempty lists of transactions and of withdrawals.
    bodies = [rlp.decode(bytes.fromhex(c["rlp"])) for c in CASES]
    assert any(b[1] == [] for b in bodies) and any(b[1] != [] for b in bodies)
    later = [b for b, c in zip(bodies, CASES) if c["network"] not in BEFORE_SHANGHAI]
    assert any(b[3] == [] for b in later) and any(b[3] != [] for b in later)
    assert any(b[0][4] == EMPTY_TRIE_ROOT for b in bodies)
    # Each type of typed transaction appears, as its type then its payload.
    types = {tx[0] for b in bodies for tx in b[1] if isinstance(tx, bytes)}
    assert types == {1, 2, 3, 4}


def test_legacy_transaction_in_bytes_before_glamsterdam() -> None:
    case = next(c for c in CASES if c["network"] == "Prague")
    block = rlp.decode(bytes.fromhex(case["rlp"]))
    # Before Glamsterdam, a byte string that holds a legacy transaction is no transaction.
    block[1] = [rlp.encode([b"", b"", b"", b"", b"", b"", b"", b"", b""])]
    with pytest.raises(blocks.BlockError, match="unsupportedType 201") as error:
        blocks.transactions_root("pectra", rlp.encode(block))
    assert error.value.code == 0


def test_legacy_transaction_in_bytes_from_glamsterdam() -> None:
    cases = [c for c in CASES if c["network"] == "Amsterdam"
             and any(isinstance(tx, list) for tx in rlp.decode(bytes.fromhex(c["rlp"]))[1])]
    assert cases, "no vendored Amsterdam block holds a legacy transaction"
    case = cases[0]
    block = rlp.decode(bytes.fromhex(case["rlp"]))
    root = block[0][4]
    # From Glamsterdam, each legacy transaction may come as the byte string of its encoding.
    block[1] = [rlp.encode(tx) if isinstance(tx, list) else tx for tx in block[1]]
    assert blocks.transactions_root("glamsterdam", rlp.encode(block)) == root
    # The first byte 0xff is a type that no fork has.
    block[1] = [b"\xff" + rlp.encode(tx)[1:] for tx in block[1][:1]]
    with pytest.raises(blocks.BlockError, match="unsupportedType 255"):
        blocks.transactions_root("glamsterdam", rlp.encode(block))


def test_trailing_byte_rejected() -> None:
    case = CASES[0]
    block = bytes.fromhex(case["rlp"])
    with pytest.raises(ValueError):
        blocks.reencode(FORK_OF_NETWORK[case["network"]], block + b"\x00")


def test_unknown_fork_rejected() -> None:
    with pytest.raises(ValueError):
        blocks.reencode("prague", bytes.fromhex(CASES[0]["rlp"]))


def test_rejects_non_bytes() -> None:
    with pytest.raises(TypeError):
        blocks.reencode("frontier", "c0")  # type: ignore[arg-type]
