"""The slashing protection of EIP-3076 against its conditions and the interchange tests."""

import json
from pathlib import Path

import pytest

from ethlib import consensus
from raising import raises

ERROR = consensus.SlashingProtectionError

GVR = "0x" + "04" * 32
KEY = "0x" + "a1" * 48
OTHER_KEY = "0x" + "b2" * 48
ROOT_A = "0x" + "aa" * 32
ROOT_B = "0x" + "bb" * 32


def interchange(data: list, root: str = GVR, version: str = "5") -> bytes:
    """The JSON text of an interchange file."""
    metadata = {"interchange_format_version": version, "genesis_validators_root": root}
    return json.dumps({"metadata": metadata, "data": data}).encode()


def entry(pubkey: str = KEY, blocks: list | None = None, attestations: list | None = None) -> dict:
    return {
        "pubkey": pubkey,
        "signed_blocks": blocks or [],
        "signed_attestations": attestations or [],
    }


def block(slot: int, root: str | None = None) -> dict:
    record = {"slot": str(slot)}
    if root is not None:
        record["signing_root"] = root
    return record


def vote(source: int, target: int, root: str | None = None) -> dict:
    record = {"source_epoch": str(source), "target_epoch": str(target)}
    if root is not None:
        record["signing_root"] = root
    return record


def _bytes(text: str) -> bytes:
    return bytes.fromhex(text.removeprefix("0x"))


# ---- Reading and writing the file ----------------------------------------------------------------


def test_read_writes_the_file_again():
    # Upper-case hex, a field that the format does not name, and a record without a root.
    text = json.dumps(
        {
            "metadata": {
                "interchange_format_version": "5",
                "genesis_validators_root": GVR,
            },
            "data": [
                {
                    **entry(
                        KEY.upper().replace("0X", "0x"),
                        blocks=[block(9, ROOT_A), block(3)],
                        attestations=[vote(1, 2)],
                    ),
                    "comment": "ignored",
                }
            ],
        }
    ).encode()
    written = json.loads(consensus.read_slashing_interchange(text))
    assert written == json.loads(
        interchange([entry(blocks=[block(9, ROOT_A), block(3)], attestations=[vote(1, 2)])])
    )


@pytest.mark.parametrize(
    ("text", "code", "message"),
    [
        (b"\xff", 0, "the interchange is not UTF-8"),
        (b"{", 0, "the interchange is not JSON"),
        (interchange([], version="4"), 2, "slashing protection failed with code 2"),
        (b'{"data": []}', 1, "slashing protection failed with code 1"),
        (interchange([], root="0x" + "04" * 31), 1, "slashing protection failed with code 1"),
        (
            interchange([entry(pubkey="0x" + "a1" * 47)]),
            1,
            "slashing protection failed with code 1",
        ),
        (
            interchange([entry(blocks=[block(1, "0x" + "aa" * 33)])]),
            1,
            "slashing protection failed with code 1",
        ),
        (
            interchange([entry(blocks=[{"slot": "01"}])]),
            1,
            "slashing protection failed with code 1",
        ),
        (
            interchange([entry(blocks=[{"slot": str(2**64)}])]),
            1,
            "slashing protection failed with code 1",
        ),
        (interchange([entry(blocks=[{"slot": 1}])]), 1, "slashing protection failed with code 1"),
        (
            interchange([entry(attestations=[{"source_epoch": "1"}])]),
            1,
            "slashing protection failed with code 1",
        ),
        (
            interchange([{"pubkey": KEY, "signed_blocks": []}]),
            1,
            "slashing protection failed with code 1",
        ),
    ],
    ids=[
        "utf8",
        "json",
        "version",
        "metadata",
        "root",
        "pubkey",
        "signing root",
        "leading zero",
        "too large",
        "number",
        "target",
        "attestations",
    ],
)
def test_read_rejected(text: bytes, code: int, message: str):
    with raises(ERROR, message) as info:
        consensus.read_slashing_interchange(text)
    assert info.value.code == code


def test_import_keeps_every_record():
    held = interchange([entry(blocks=[block(1, ROOT_A)])])
    file = interchange([entry(attestations=[vote(2, 3)]), entry(OTHER_KEY)], root="0x" + "00" * 32)
    merged = json.loads(consensus.import_slashing_interchange(held, file))
    # The held file keeps its chain, and the entries of the file come after its own.
    assert merged == json.loads(
        interchange(
            [entry(blocks=[block(1, ROOT_A)]), entry(attestations=[vote(2, 3)]), entry(OTHER_KEY)]
        )
    )


# ---- The conditions on blocks --------------------------------------------------------------------


def _check_block(record: list, slot: int, root: str = ROOT_A, key: str = KEY) -> None:
    consensus.check_block_signing(interchange(record), _bytes(key), slot, _bytes(root))


@pytest.mark.parametrize(
    ("record", "slot", "root"),
    [
        ([], 0, ROOT_A),
        ([entry(blocks=[block(5, ROOT_A)])], 6, ROOT_B),
        # A repeat of a recorded block may be signed again.
        ([entry(blocks=[block(5, ROOT_A)])], 5, ROOT_A),
        # The blocks of another key do not count.
        ([entry(OTHER_KEY, blocks=[block(5)])], 5, ROOT_A),
    ],
    ids=["empty", "later", "repeat", "other key"],
)
def test_block_signed(record: list, slot: int, root: str):
    _check_block(record, slot, root)


@pytest.mark.parametrize(
    ("record", "slot", "root", "code"),
    [
        # Condition 1: another block of the slot, or a recorded one without a root.
        ([entry(blocks=[block(5, ROOT_A)])], 5, ROOT_B, 3),
        ([entry(blocks=[block(5)])], 5, ROOT_A, 3),
        # Condition 2: a slot at most the least recorded slot.
        ([entry(blocks=[block(5, ROOT_A), block(9, ROOT_B)])], 4, ROOT_B, 4),
        # The least slot reads every entry of the key.
        ([entry(blocks=[block(9, ROOT_A)]), entry(blocks=[block(3)])], 2, ROOT_B, 4),
    ],
    ids=["other root", "no root", "below", "two entries"],
)
def test_block_refused(record: list, slot: int, root: str, code: int):
    with raises(ERROR, f"slashing protection failed with code {code}") as info:
        _check_block(record, slot, root)
    assert info.value.code == code


def test_recorded_block_refuses_another_block_of_its_slot():
    record = consensus.record_block_signing(interchange([]), _bytes(KEY), 7, _bytes(ROOT_A))
    consensus.check_block_signing(record, _bytes(KEY), 7, _bytes(ROOT_A))
    with raises(ERROR, "slashing protection failed with code 3"):
        consensus.check_block_signing(record, _bytes(KEY), 7, _bytes(ROOT_B))


# ---- The conditions on votes ---------------------------------------------------------------------


def _check_vote(record: list, source: int, target: int, root: str = ROOT_A) -> None:
    consensus.check_attestation_signing(
        interchange(record), _bytes(KEY), source, target, _bytes(root)
    )


@pytest.mark.parametrize(
    ("record", "source", "target", "root"),
    [
        ([], 0, 0, ROOT_A),
        ([entry(attestations=[vote(2, 3, ROOT_A)])], 3, 4, ROOT_B),
        ([entry(attestations=[vote(2, 3, ROOT_A)])], 2, 3, ROOT_A),
    ],
    ids=["empty", "later", "repeat"],
)
def test_vote_signed(record: list, source: int, target: int, root: str):
    _check_vote(record, source, target, root)


@pytest.mark.parametrize(
    ("record", "source", "target", "root", "code"),
    [
        # Condition 3: a double vote, by root or without a recorded root, and the two surrounds.
        ([entry(attestations=[vote(2, 5, ROOT_A)])], 3, 5, ROOT_B, 5),
        ([entry(attestations=[vote(2, 5)])], 2, 5, ROOT_A, 5),
        ([entry(attestations=[vote(2, 5, ROOT_A)])], 1, 6, ROOT_B, 5),
        ([entry(attestations=[vote(1, 9, ROOT_A)])], 2, 8, ROOT_B, 5),
        # Condition 4: a source below the least recorded source.
        ([entry(attestations=[vote(4, 9, ROOT_A)])], 3, 10, ROOT_B, 6),
        # Condition 5: a target at most the least recorded target.
        ([entry(attestations=[vote(4, 9, ROOT_A), vote(4, 12, ROOT_A)])], 5, 8, ROOT_B, 7),
    ],
    ids=["double", "no root", "surrounds", "surrounded", "source", "target"],
)
def test_vote_refused(record: list, source: int, target: int, root: str, code: int):
    with raises(ERROR, f"slashing protection failed with code {code}") as info:
        _check_vote(record, source, target, root)
    assert info.value.code == code


def test_recorded_vote_refuses_a_double_vote():
    record = consensus.record_attestation_signing(
        interchange([]), _bytes(KEY), 3, 4, _bytes(ROOT_A)
    )
    with raises(ERROR, "slashing protection failed with code 5"):
        consensus.check_attestation_signing(record, _bytes(KEY), 3, 4, _bytes(ROOT_B))


# ---- Inputs at the boundary ----------------------------------------------------------------------

_SIGNERS = [
    lambda text, key, root: consensus.check_block_signing(text, key, 1, root),
    lambda text, key, root: consensus.check_attestation_signing(text, key, 1, 2, root),
    lambda text, key, root: consensus.record_block_signing(text, key, 1, root),
    lambda text, key, root: consensus.record_attestation_signing(text, key, 1, 2, root),
]


@pytest.mark.parametrize(
    "sign", _SIGNERS, ids=["check block", "check vote", "record block", "record vote"]
)
def test_signing_inputs_rejected(sign):
    text = interchange([])
    with raises(ERROR, "the public key is 48 bytes, not 47") as info:
        sign(text, bytes(47), bytes(32))
    assert info.value.code == 0
    with raises(ERROR, "the signing root is 32 bytes, not 31") as info:
        sign(text, bytes(48), bytes(31))
    assert info.value.code == 0
    with raises(ERROR, "the interchange is not JSON") as info:
        sign(b"[", bytes(48), bytes(32))
    assert info.value.code == 0
    with raises(ERROR, "slashing protection failed with code 2") as info:
        sign(interchange([], version="4"), bytes(48), bytes(32))
    assert info.value.code == 2


def test_import_of_a_file_that_does_not_read():
    with raises(ERROR, "the interchange is not JSON"):
        consensus.import_slashing_interchange(interchange([]), b"")
    with raises(ERROR, "slashing protection failed with code 2"):
        consensus.import_slashing_interchange(interchange([], version="4"), interchange([]))


# ---- The interchange tests -----------------------------------------------------------------------

# The interchange tests of eth-clients/slashing-protection-interchange-tests at commit
# bb7900688eecd287d8723154faac6addb5e63336, the release v5.3.0, from its source archive.
ARCHIVE = "slashing-protection-interchange-tests@bb790068/source"
ARCHIVE_ROOT = "slashing-protection-interchange-tests-bb7900688eecd287d8723154faac6addb5e63336"
GENERATED = f"{ARCHIVE_ROOT}/tests/generated"


def _run(case: dict) -> None:
    """Run a case as a signer that keeps every message, the complete strategy of the tests."""
    held = interchange([], root=case["genesis_validators_root"])
    for step in case["steps"]:
        file = step["interchange"]
        # The tests refuse a file of another chain, a check that the EIP does not make.
        if file["metadata"]["genesis_validators_root"] != case["genesis_validators_root"]:
            assert not step["should_succeed"]
            return
        assert step["should_succeed"]
        held = consensus.import_slashing_interchange(held, json.dumps(file).encode())
        for signing in step["blocks"]:
            expected = signing.get("should_succeed_complete", signing["should_succeed"])
            key, root, slot = (
                _bytes(signing["pubkey"]),
                _bytes(signing["signing_root"]),
                int(signing["slot"]),
            )
            try:
                consensus.check_block_signing(held, key, slot, root)
            except ERROR:
                assert not expected, (case["name"], signing)
                continue
            assert expected, (case["name"], signing)
            held = consensus.record_block_signing(held, key, slot, root)
        for signing in step["attestations"]:
            expected = signing.get("should_succeed_complete", signing["should_succeed"])
            key, root = _bytes(signing["pubkey"]), _bytes(signing["signing_root"])
            source, target = int(signing["source_epoch"]), int(signing["target_epoch"])
            try:
                consensus.check_attestation_signing(held, key, source, target, root)
            except ERROR:
                assert not expected, (case["name"], signing)
                continue
            assert expected, (case["name"], signing)
            held = consensus.record_attestation_signing(held, key, source, target, root)


@pytest.mark.archive(ARCHIVE, GENERATED)
def test_interchange_tests(archive: Path):
    cases = sorted((archive / GENERATED).glob("*.json"))
    assert len(cases) == 38
    for path in cases:
        _run(json.loads(path.read_text()))
