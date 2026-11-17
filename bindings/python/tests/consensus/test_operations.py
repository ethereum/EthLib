"""The block operations of EthLib against the operations vectors of consensus-specs."""

import hashlib
from pathlib import Path

import pytest
from ruamel.yaml import YAML

import archives
from ethlib import consensus
from ethlib.networking import snappy
from ethlib.serialization import ssz
from raising import raises

from .containers import FORKS
from .test_data_column import replacements

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "operations"

# The file of the operation of each handler, and the forks whose rule EthLib holds.
# Electra changes attestations and exits, Deneb the signature of exits, and Gloas attestations.
# Gloas moves the execution payload out of the block, and Heze keeps the Gloas rules.
# From Gloas the withdrawals take no payload, so their cases have no operation file.
HANDLERS = {
    "block_header": (
        "block",
        ("phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas", "heze"),
    ),
    "proposer_slashing": (
        "proposer_slashing",
        ("phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas", "heze"),
    ),
    "attester_slashing": (
        "attester_slashing",
        ("phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas", "heze"),
    ),
    "attestation": (
        "attestation",
        ("phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas", "heze"),
    ),
    "deposit": ("deposit", ("phase0", "altair", "bellatrix", "capella", "deneb", "electra")),
    "deposit_request": ("deposit_request", ("electra", "fulu", "gloas", "heze")),
    "withdrawal_request": ("withdrawal_request", ("electra", "fulu", "gloas", "heze")),
    "consolidation_request": ("consolidation_request", ("electra", "fulu", "gloas", "heze")),
    "sync_aggregate": (
        "sync_aggregate",
        ("altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas", "heze"),
    ),
    "voluntary_exit": (
        "voluntary_exit",
        ("phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas", "heze"),
    ),
    "voluntary_exit_churn": ("voluntary_exit", ("gloas", "heze")),
    "execution_payload": ("body", ("bellatrix", "capella", "deneb", "electra", "fulu")),
    "withdrawals": ("execution_payload", ("capella", "deneb", "electra", "fulu", "gloas", "heze")),
    "bls_to_execution_change": (
        "address_change",
        ("capella", "deneb", "electra", "fulu", "gloas", "heze"),
    ),
    "payload_attestation": ("payload_attestation", ("gloas", "heze")),
    "execution_payload_bid": ("execution_payload_bid", ("gloas", "heze")),
    "builder_deposit_request": ("builder_deposit_request", ("gloas", "heze")),
    "builder_exit_request": ("builder_exit_request", ("gloas", "heze")),
    "parent_execution_payload": ("block", ("gloas", "heze")),
}

# The release archives, and the forks whose archived cases this file runs.
ARCHIVES = {
    "minimal": "consensus-specs/v1.7.0-beta.4/minimal",
    "mainnet": "consensus-specs/v1.7.0-beta.4/mainnet",
}
ARCHIVE_FORKS = ("electra", "fulu", "gloas", "heze")


def runs(fork: str, handler: str) -> bool:
    """Whether EthLib runs the cases of a handler at a fork."""
    return handler in HANDLERS and fork in HANDLERS[handler][1]


def run_case(preset: str, fork: str, handler: str, case: Path) -> None:
    """Run one case: the state after the operation, or a rejection when the case has no post."""
    pre = snappy.decompress((case / "pre.ssz_snappy").read_bytes())
    if handler == "withdrawals" and fork in ("gloas", "heze"):
        operation = b""
    else:
        operation = snappy.decompress((case / f"{HANDLERS[handler][0]}.ssz_snappy").read_bytes())
    meta_file = case / "meta.yaml"
    meta = (YAML(typ="safe").load(meta_file.read_text()) if meta_file.exists() else None) or {}
    # Setting 2 marks placeholder signatures, which the case must not check.
    setting = meta.get("bls_setting", 0)
    # For a Gloas attestation, the export takes the parent block from the state.
    # That parent block is the latest block header of the state.
    # The slot of that header starts at byte 64 of the state.
    if "parent_slot" in meta:
        assert meta["parent_slot"] == int.from_bytes(pre[64:72], "little")
    config_file = case / "config.yaml"
    config = (
        replacements(YAML(typ="safe").load(config_file.read_text()), preset)
        if config_file.exists()
        else None
    )
    # The answer of the execution layer to a payload, which the case fixes.
    execution = case / "execution.yaml"
    valid = (
        YAML(typ="safe").load(execution.read_text())["execution_valid"]
        if execution.exists()
        else True
    )
    post = case / "post.ssz_snappy"
    if post.exists():
        got = consensus.process_operation(
            preset, FORKS[fork], handler, pre, operation, setting != 2, config, valid
        )
        assert got == snappy.decompress(post.read_bytes())
    else:
        with pytest.raises(consensus.TransitionError):
            consensus.process_operation(
                preset, FORKS[fork], handler, pre, operation, setting != 2, config, valid
            )


def _cases() -> list:
    """Every vendored case, as its preset, fork, handler and directory."""
    cases = []
    for pre in sorted(FILES.rglob("pre.ssz_snappy")):
        case = pre.parent
        preset, fork, _, handler = case.relative_to(FILES).parts[:4]
        cases.append(
            pytest.param(preset, fork, handler, case, id=case.relative_to(FILES).as_posix())
        )
    return cases


def _archive_cases() -> list:
    """Every case of the archives for a handler that EthLib runs there, when the cache is set."""
    if archives.CACHE is None:
        return []
    cases = []
    for preset, name in ARCHIVES.items():
        paths = [
            f"tests/{preset}/{fork}/operations/{handler}"
            for fork in ARCHIVE_FORKS
            for handler in HANDLERS
            if runs(fork, handler)
        ]
        base = archives.unpack(name, *paths) / "tests" / preset
        for path in paths:
            for pre in sorted((base / path.split("/", 2)[2]).rglob("pre.ssz_snappy")):
                case = pre.parent
                fork, _, handler = case.relative_to(base).parts[:3]
                cases.append(
                    pytest.param(
                        preset,
                        fork,
                        handler,
                        case,
                        id=f"{preset}/{case.relative_to(base).as_posix()}",
                        marks=pytest.mark.archive(name),
                    )
                )
    # An empty list would skip the test in silence, so a wrong path in an archive fails here.
    if not cases:
        raise LookupError("the archives hold no operations case of a handler that EthLib runs")
    return cases


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text().splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    assert len(entries) == sum(
        1
        for path in FILES.rglob("*")
        if path.is_file() and path.name not in ("SHA256SUMS", "README.md")
    )
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


@pytest.mark.parametrize("preset, fork, handler, case", _cases())
def test_case(preset, fork, handler, case):
    assert runs(fork, handler)
    run_case(preset, fork, handler, case)


@archives.parametrize("preset, fork, handler, case", _archive_cases)
def test_archive_case(preset, fork, handler, case):
    run_case(preset, fork, handler, case)


def test_no_deposit_from_gloas():
    # A Gloas block holds no deposit, so the operation fails before it reads the state.
    with raises(consensus.TransitionError, "no operation deposit at glamsterdam") as info:
        consensus.process_operation("minimal", "glamsterdam", "deposit", b"", b"")
    assert info.value.code == 0


def test_undecodable_state():
    with raises(
        consensus.TransitionError,
        "input rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 7057 0",
    ) as info:
        consensus.process_operation("minimal", "phase0", "block_header", b"", b"")
    assert info.value.code == 0


def test_payload_rejected_by_the_execution_layer():
    # A payload that every check of the beacon chain accepts fails when the execution layer says no.
    case = (
        FILES
        / "minimal"
        / "bellatrix"
        / "operations"
        / "execution_payload"
        / "pyspec_tests"
        / "success_regular_payload"
    )
    pre = snappy.decompress((case / "pre.ssz_snappy").read_bytes())
    body = snappy.decompress((case / "body.ssz_snappy").read_bytes())
    # The offset of the payload follows the fixed fields of the body and five list offsets.
    # Those are the reveal, the eth1 data, the graffiti and a minimal sync aggregate of 100 bytes.
    payload = body[int.from_bytes(body[320:324], "little") :]
    # The block hash follows 472 bytes, from the parent hash to the base fee, with one offset.
    block_hash = payload[472:504]
    with raises(
        consensus.TransitionError,
        f"EthLib.Consensus.TransitionError.invalidExecutionPayload 0x{block_hash.hex()}",
    ) as info:
        consensus.process_operation(
            "minimal", "bellatrix", "execution_payload", pre, body, execution_valid=False
        )
    assert info.value.code == 69


def test_no_payload_before_bellatrix():
    with raises(
        consensus.TransitionError,
        "input rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 10229 0",
    ) as info:
        consensus.process_operation("minimal", "altair", "execution_payload", b"", b"")
    assert info.value.code == 0


# A beacon block header, as SSZ describes it.
HEADER = {
    "container": [
        ["slot", {"uint": 8}],
        ["proposer_index", {"uint": 8}],
        ["parent_root", {"byte_vector": 32}],
        ["state_root", {"byte_vector": 32}],
        ["body_root", {"byte_vector": 32}],
    ]
}

# Each error message starts with the name of its constructor.
REJECTED = "EthLib.Consensus.TransitionError."


def vector(fork: str, handler: str, name: str) -> tuple[bytes, bytes]:
    """The state and the operation of a vendored minimal case."""
    case = FILES / "minimal" / fork / "operations" / handler / "pyspec_tests" / name
    pre = snappy.decompress((case / "pre.ssz_snappy").read_bytes())
    operation = snappy.decompress((case / f"{HANDLERS[handler][0]}.ssz_snappy").read_bytes())
    return pre, operation


def u64(data: bytes, offset: int) -> int:
    """The little-endian uint64 at an offset."""
    return int.from_bytes(data[offset : offset + 8], "little")


def header_root(data: bytes) -> bytes:
    """The hash tree root of the SSZ bytes of a block header."""
    return ssz.hash_tree_root(HEADER, ssz.deserialize(HEADER, data))


def test_wrong_parent_carries_both_roots():
    pre, block = vector("phase0", "block_header", "basic_block_header")
    # The latest block header of a state is at bytes 64 to 176.
    # It follows genesis_time, genesis_validators_root, slot and fork.
    expected = header_root(pre[64:176])
    # A block starts with its slot and its proposer index, then its parent root.
    forged = block[:16] + bytes(32) + block[48:]
    message = f"{REJECTED}wrongParent 0x{'00' * 32} 0x{expected.hex()}"
    with raises(consensus.TransitionError, message) as info:
        consensus.process_operation("minimal", "phase0", "block_header", pre, forged, False)
    assert info.value.code == 6


def test_proposer_slashing_headers_disagree():
    pre, slashing = vector("phase0", "proposer_slashing", "basic")
    # A slashing holds two signed headers of 208 bytes: a header of 112 bytes, then a signature.
    slot, proposer = u64(slashing, 0), u64(slashing, 8)
    other_slot = slashing[:208] + (slot + 1).to_bytes(8, "little") + slashing[216:]
    message = f"{REJECTED}headerSlotsDiffer {slot} {slot + 1}"
    with raises(consensus.TransitionError, message) as info:
        consensus.process_operation(
            "minimal", "phase0", "proposer_slashing", pre, other_slot, False
        )
    assert info.value.code == 10
    other_proposer = slashing[:216] + (proposer + 1).to_bytes(8, "little") + slashing[224:]
    message = f"{REJECTED}headerProposersDiffer {proposer} {proposer + 1}"
    with raises(consensus.TransitionError, message) as info:
        consensus.process_operation(
            "minimal", "phase0", "proposer_slashing", pre, other_proposer, False
        )
    assert info.value.code == 11
    message = f"{REJECTED}sameHeaders {slot} {proposer}"
    with raises(consensus.TransitionError, message) as info:
        consensus.process_operation(
            "minimal", "phase0", "proposer_slashing", pre, slashing[:208] * 2, False
        )
    assert info.value.code == 12


def signing_root(pre: bytes, object_root: bytes, domain_type: int, epoch: int) -> bytes:
    """The root that a signature signs: an object root under the domain of the state's fork."""
    # The fork of a state follows genesis_time, genesis_validators_root and slot.
    previous, current, fork_epoch = pre[48:52], pre[52:56], u64(pre, 56)
    version = previous if epoch < fork_epoch else current
    # A domain is its type, then 28 bytes of the root of the fork version and the genesis root.
    fork_data_root = hashlib.sha256(version + bytes(28) + pre[8:40]).digest()
    domain = domain_type.to_bytes(4, "little") + fork_data_root[:28]
    return hashlib.sha256(object_root + domain).digest()


def test_header_signature_carries_the_signing_root():
    pre, slashing = vector("phase0", "proposer_slashing", "invalid_incorrect_sig_1")
    # A minimal epoch has 8 slots, and the proposer domain has type 0.
    root = signing_root(pre, header_root(slashing[:112]), 0, u64(slashing, 0) // 8)
    message = f"{REJECTED}invalidHeaderSignature {u64(slashing, 8)} 0x{root.hex()}"
    with raises(consensus.TransitionError, message) as info:
        consensus.process_operation("minimal", "phase0", "proposer_slashing", pre, slashing)
    assert info.value.code == 14


def test_attester_slashing_of_one_vote():
    pre, slashing = vector("phase0", "attester_slashing", "basic_double")
    # A slashing holds the offsets of its two attestations, then the attestations.
    start, end = int.from_bytes(slashing[:4], "little"), int.from_bytes(slashing[4:8], "little")
    first = slashing[start:end]
    forged = (8).to_bytes(4, "little") + (8 + len(first)).to_bytes(4, "little") + first * 2
    # The data of an attestation follows the offset of its indices.
    # Its source epoch is at byte 48 of the data, and its target epoch at byte 88.
    source, target = u64(first, 52), u64(first, 92)
    message = f"{REJECTED}notSlashableData {source} {target} {source} {target}"
    with raises(consensus.TransitionError, message) as info:
        consensus.process_operation("minimal", "phase0", "attester_slashing", pre, forged, False)
    assert info.value.code == 15


@pytest.mark.parametrize(
    ("fork", "name"),
    [("gloas", "invalid_too_many_attesting_indices"), ("heze", "invalid_all_empty_indices")],
)
def test_invalid_indexed_attestation_names_its_position(fork, name):
    pre, slashing = vector(fork, "attester_slashing", name)
    with raises(consensus.TransitionError, f"{REJECTED}invalidIndexedAttestation 1") as info:
        consensus.process_operation("minimal", FORKS[fork], "attester_slashing", pre, slashing)
    assert info.value.code == 16


def test_invalid_second_attestation_names_position_two():
    pre, slashing = vector("phase0", "attester_slashing", "basic_double")
    end = int.from_bytes(slashing[4:8], "little")
    # An attestation holds the offset of its indices, its data and its signature in 228 bytes.
    # Without the indices that follow, the second attestation names no validator.
    forged = slashing[: end + 228]
    message = f"{REJECTED}invalidIndexedAttestation 2"
    with raises(consensus.TransitionError, message) as info:
        consensus.process_operation("minimal", "phase0", "attester_slashing", pre, forged, False)
    assert info.value.code == 16


# Deposit data, as SSZ describes it.
DEPOSIT_DATA = {
    "container": [
        ["pubkey", {"byte_vector": 48}],
        ["withdrawal_credentials", {"byte_vector": 32}],
        ["amount", {"uint": 8}],
        ["signature", {"byte_vector": 96}],
    ]
}


def test_bad_deposit_proof_carries_the_roots():
    pre, deposit = vector("phase0", "deposit", "invalid_bad_merkle_proof")
    # A minimal phase0 state holds its eth1 data at byte 4276.
    # It follows the 64 block roots, the 64 state roots and the offset of the historical roots.
    # The deposit root starts the eth1 data; the deposit index follows the eth1 data and an offset.
    deposit_root, index = pre[4276:4308], u64(pre, 4352)
    # A deposit holds a branch of 33 roots, then its data.
    data = deposit[33 * 32 :]
    leaf = ssz.hash_tree_root(DEPOSIT_DATA, ssz.deserialize(DEPOSIT_DATA, data))
    message = f"{REJECTED}invalidDepositProof {index} 0x{leaf.hex()} 0x{deposit_root.hex()}"
    with raises(consensus.TransitionError, message) as info:
        consensus.process_operation("minimal", "phase0", "deposit", pre, deposit)
    assert info.value.code == 44


def test_bad_exit_signature_carries_the_signing_root():
    pre, signed = vector("phase0", "voluntary_exit", "invalid_incorrect_signature")
    # An exit holds its epoch and the index of its validator, each a chunk of its root.
    epoch, index = u64(signed, 0), u64(signed, 8)
    exit_root = hashlib.sha256(signed[:8] + bytes(24) + signed[8:16] + bytes(24)).digest()
    # The domain of a voluntary exit has type 4.
    root = signing_root(pre, exit_root, 4, epoch)
    message = f"{REJECTED}invalidExitSignature {index} 0x{root.hex()}"
    with raises(consensus.TransitionError, message) as info:
        consensus.process_operation("minimal", "phase0", "voluntary_exit", pre, signed)
    assert info.value.code == 50


def test_bad_sync_aggregate_carries_the_signing_root():
    pre, aggregate = vector("altair", "sync_aggregate", "invalid_signature_bad_domain")
    # The members sign the root of the block at the slot before the state's.
    # A minimal state keeps 64 block roots from byte 176.
    slot = u64(pre, 40) - 1
    block_root = pre[176 + 32 * (slot % 64) : 176 + 32 * (slot % 64 + 1)]
    # The domain of the sync committee has type 7, at the epoch of that slot.
    root = signing_root(pre, block_root, 7, slot // 8)
    # A minimal sync committee has 32 members, one bit each in the first 4 bytes.
    participants = int.from_bytes(aggregate[:4], "little").bit_count()
    message = f"{REJECTED}invalidSyncAggregate {slot} {participants} 0x{root.hex()}"
    with raises(consensus.TransitionError, message) as info:
        consensus.process_operation("minimal", "altair", "sync_aggregate", pre, aggregate)
    assert info.value.code == 71


@pytest.mark.parametrize("fork", ["capella", "electra"])
def test_wrong_withdrawals_names_the_first_difference(fork):
    # The payload carries the one expected partial withdrawal, with a wrong amount.
    # The lists then differ at position 0, and each holds one withdrawal.
    pre, payload = vector(fork, "withdrawals", "invalid_incorrect_amount_partial")
    with raises(consensus.TransitionError, f"{REJECTED}wrongWithdrawals 0 1 1") as info:
        consensus.process_operation("minimal", FORKS[fork], "withdrawals", pre, payload)
    assert info.value.code == 62


def test_wrong_attestation_source_carries_both_checkpoints():
    pre, attestation = vector("phase0", "attestation", "one_basic_attestation")
    # An attestation holds the offset of its bits, then its data.
    # The source checkpoint is at bytes 48 to 88 of the data: an epoch, then a root.
    source_epoch, source_root = u64(attestation, 52), attestation[60:92]
    forged = attestation[:60] + b"\x11" * 32 + attestation[92:]
    # The valid attestation votes for the justified checkpoint that the check expects.
    message = (
        f"{REJECTED}wrongAttestationSource {source_epoch} 0x{'11' * 32} "
        f"{source_epoch} 0x{source_root.hex()}"
    )
    with raises(consensus.TransitionError, message) as info:
        consensus.process_operation("minimal", "phase0", "attestation", pre, forged, False)
    assert info.value.code == 40


def test_bad_attestation_signature_names_its_attesters():
    pre, attestation = vector("phase0", "attestation", "one_basic_attestation")
    # The signature follows the offset and the data; the aggregation bits come last.
    forged = attestation[:132] + bytes(96) + attestation[228:]
    bits = attestation[228:]
    # The last set bit of a bit list marks its length, so it names no attester.
    attesters = sum(byte.bit_count() for byte in bits) - 1
    data_slot = u64(attestation, 4)
    message = f"{REJECTED}invalidAttestation {data_slot} {attesters}"
    with raises(consensus.TransitionError, message) as info:
        consensus.process_operation("minimal", "phase0", "attestation", pre, forged)
    assert info.value.code == 42


def test_paid_self_built_bid_carries_its_value():
    pre, signed = vector(
        "heze", "execution_payload_bid", "process_execution_payload_bid_self_build_non_zero_value"
    )
    # A signed bid holds the offset of the bid, then the signature.
    bid = int.from_bytes(signed[:4], "little")
    # The value of a bid is at byte 172.
    # It follows four hashes, the fee recipient, the gas limit, the builder and the slot.
    message = f"{REJECTED}selfBuildBidPaid {u64(signed, bid + 172)}"
    with raises(consensus.TransitionError, message) as info:
        consensus.process_operation("minimal", "hegota", "execution_payload_bid", pre, signed)
    assert info.value.code == 21
