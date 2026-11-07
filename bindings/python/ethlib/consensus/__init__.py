"""The consensus layer: presets, configurations, containers, the shuffle, custody and networking."""

import json
import struct
from typing import Any

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import (
    ConsensusError,
    ForkChoiceError,
    LightClientError,
    ProposerError,
    TransitionError,
    ValidatorDutyError,
    WeakSubjectivityError,
)


def _value(value: Any) -> Any:
    # The export writes every integer as a string of decimal digits.
    if isinstance(value, str) and not value.startswith("0x") and value.isdigit():
        return int(value)
    if isinstance(value, list):
        return [_value(item) for item in value]
    if isinstance(value, dict):
        return {key: _value(item) for key, item in value.items()}
    return value


def preset(name: str) -> dict:
    """The values of a preset, with the values that it derives from them."""
    return _value(json.loads(_native.consensus_preset(name)))


def config(name: str) -> dict:
    """The values of a configuration."""
    return _value(json.loads(_native.consensus_config(name)))


def parameters(name: str, fork: str) -> dict:
    """The values of a preset that a fork replaces, as they stand at the fork."""
    return _value(json.loads(_native.consensus_parameters(name, fork)))


def get_custody_groups(node_id: int, custody_group_count: int, name: str = "mainnet") -> list:
    """The sorted custody groups of a node, or ConsensusError when they cannot be selected."""
    if not 0 <= node_id < 2**256 or not 0 <= custody_group_count < 2**64:
        raise OverflowError("node_id or custody_group_count is out of range")
    groups = _native.consensus_get_custody_groups(
        name, node_id.to_bytes(32, "big"), custody_group_count
    )
    return _value(json.loads(groups))


def compute_columns_for_custody_group(custody_group: int, name: str = "mainnet") -> list:
    """The columns of a custody group, or ConsensusError for a group out of range."""
    if not 0 <= custody_group < 2**64:
        raise OverflowError("custody_group is out of range")
    columns = _native.consensus_compute_columns_for_custody_group(name, custody_group)
    return _value(json.loads(columns))


def ssz_static(name: str, fork: str, type_name: str, data: bytes) -> tuple[bytes, bytes]:
    """The root of the beacon container that SSZ bytes encode, and its bytes encoded again."""
    out = _native.consensus_ssz_static(name, fork, type_name, data)
    return out[:32], out[32:]


def pq_keys_ssz(type_name: str, data: bytes) -> tuple[bytes, bytes]:
    """The root of the EIP-8450 container that SSZ bytes encode, and its bytes encoded again."""
    out = _native.pq_keys_ssz(type_name, data)
    return out[:32], out[32:]


def pq_keys_possession_signing_root(
    genesis_validators_root: bytes, pubkey: bytes, xmss_public_key: bytes, name: str = "mainnet"
) -> bytes:
    """The root that an EIP-8450 proof of possession signs."""
    return _native.pq_keys_possession_signing_root(
        name, genesis_validators_root, pubkey, xmss_public_key
    )


def pq_keys_is_valid_possession_proof(
    genesis_validators_root: bytes,
    pubkey: bytes,
    xmss_public_key: bytes,
    proof: bytes,
    name: str = "mainnet",
) -> bool:
    """Whether an EIP-8450 proof of possession is valid."""
    return _native.pq_keys_is_valid_possession_proof(
        name, genesis_validators_root, pubkey, xmss_public_key, proof
    )


def compute_shuffled_permutation(count: int, seed: bytes, name: str = "mainnet") -> list:
    """The shuffled position of every index below the count."""
    return _value(json.loads(_native.consensus_compute_shuffled_permutation(name, count, seed)))


def compute_shuffled_index(index: int, count: int, seed: bytes, name: str = "mainnet") -> int:
    """The shuffled position of one index, or ConsensusError when it is not below the count."""
    return _native.consensus_compute_shuffled_index(name, index, count, seed)


def reqresp_protocol_ids(fork: str) -> list:
    """The request and response protocol IDs of a fork."""
    return json.loads(_native.consensus_reqresp_protocol_ids(fork))


def reqresp_parse_protocol_id(text: str) -> tuple[str, int]:
    """The protocol name and the version that a protocol ID names."""
    name, version = json.loads(_native.consensus_reqresp_parse_protocol_id(text))
    return name, version


def reqresp_message(name: str, fork: str, type_name: str, data: bytes) -> tuple[bytes, bytes]:
    """The root of a request or response message that SSZ bytes encode, and its bytes again."""
    out = _native.consensus_reqresp_message(name, fork, type_name, data)
    return out[:32], out[32:]


def compute_min_epochs_for_block_requests(name: str = "mainnet") -> int:
    """The fewest epochs back from the current one over which a node must serve blocks."""
    return _native.consensus_compute_min_epochs_for_block_requests(name)


def gossip_topics(fork: str, name: str = "mainnet") -> list:
    """The names of the gossip topics of a fork."""
    return json.loads(_native.consensus_gossip_topics(name, fork))


def compute_subnet_for_attestation(
    committees_per_slot: int, slot: int, committee_index: int, name: str = "mainnet"
) -> int:
    """The subnet of an attestation."""
    return _native.consensus_compute_subnet_for_attestation(
        name, committees_per_slot, slot, committee_index
    )


def compute_subnet_for_blob_sidecar(fork: str, blob_index: int, name: str = "mainnet") -> int:
    """The subnet of a blob sidecar at a fork."""
    return _native.consensus_compute_subnet_for_blob_sidecar(name, fork, blob_index)


def compute_subnet_for_data_column_sidecar(column_index: int, name: str = "mainnet") -> int:
    """The subnet of a data column sidecar."""
    return _native.consensus_compute_subnet_for_data_column_sidecar(name, column_index)


def compute_subscribed_subnets(node_id: int, epoch: int, name: str = "mainnet") -> list:
    """The attestation subnets of a node in an epoch."""
    if not 0 <= node_id < 2**256:
        raise OverflowError("node_id is out of range")
    subnets = _native.consensus_compute_subscribed_subnets(name, node_id.to_bytes(32, "big"), epoch)
    return _value(json.loads(subnets))


def merkle_proof(name: str, fork: str, type_name: str, data: bytes, gindex: int) -> tuple:
    """The node at a generalized index of a beacon container, and its branch up to the root."""
    out = _native.consensus_merkle_proof(name, fork, type_name, data, gindex)
    return out[:32], [out[i : i + 32] for i in range(32, len(out), 32)]


def verify_blob_sidecar_inclusion_proof(name: str, fork: str, data: bytes) -> bool:
    """Whether the branch of a blob sidecar climbs from its commitment to its body root."""
    return _native.consensus_verify_blob_sidecar_inclusion_proof(name, fork, data)


# The bytes of one matrix entry: a cell, a proof, a column index and a row index.
MATRIX_ENTRY_BYTES = 2048 + 48 + 8 + 8


def _list_items(data: bytes) -> list:
    # Split the SSZ encoding of a list of variable-size items at its offsets.
    if not data:
        return []
    first = int.from_bytes(data[:4], "little")
    offsets = [int.from_bytes(data[i : i + 4], "little") for i in range(0, first, 4)]
    return [data[a:b] for a, b in zip(offsets, offsets[1:] + [len(data)], strict=True)]


def verify_data_column_sidecar(
    name: str, fork: str, data: bytes, block: bytes = b"", config: dict | None = None
) -> bool:
    """Whether a data column sidecar has a valid shape; from Gloas, against its signed block."""
    replacements = json.dumps(config).encode() if config else b""
    return _native.consensus_verify_data_column_sidecar(name, fork, data, block, replacements)


def verify_data_column_sidecar_inclusion_proof(name: str, fork: str, data: bytes) -> bool:
    """Whether the branch of a data column sidecar climbs from its commitments to its body root."""
    return _native.consensus_verify_data_column_sidecar_inclusion_proof(name, fork, data)


def verify_data_column_sidecar_kzg_proofs(
    name: str, fork: str, data: bytes, block: bytes = b""
) -> bool:
    """Whether the cells of a data column sidecar match its commitments by their proofs."""
    return _native.consensus_verify_data_column_sidecar_kzg_proofs(name, fork, data, block)


def verify_partial_data_column_header_inclusion_proof(name: str, fork: str, data: bytes) -> bool:
    """Whether the branch of a partial data column header climbs to its body root."""
    return _native.consensus_verify_partial_data_column_header_inclusion_proof(name, fork, data)


def verify_partial_data_column_sidecar_kzg_proofs(
    name: str, fork: str, data: bytes, commitments: bytes, column_index: int
) -> bool:
    """Whether the cells of a partial data column sidecar match their commitments."""
    return _native.consensus_verify_partial_data_column_sidecar_kzg_proofs(
        name, fork, data, commitments, column_index
    )


def light_client_sync(
    name: str,
    fork: str,
    bootstrap_fork: str,
    trusted_block_root: bytes,
    genesis_validators_root: bytes,
    bootstrap: bytes,
    steps: list,
    config: dict | None = None,
) -> list:
    """The finalized and optimistic headers, as slot and two roots, after each step of a sync."""
    # A step is ("update", fork, slot, update), ("force", slot) or ("upgrade", fork).
    replacements = json.dumps(config).encode() if config else b""
    records = b"".join(_sync_step(*step) for step in steps)
    out = _native.consensus_light_client_sync(
        name,
        fork,
        bootstrap_fork,
        replacements,
        trusted_block_root,
        genesis_validators_root,
        bootstrap,
        records,
    )

    def header(record: bytes) -> tuple:
        return int.from_bytes(record[:8], "little"), record[8:40], record[40:72]

    return [
        (header(out[i : i + 72]), header(out[i + 72 : i + 144])) for i in range(0, len(out), 144)
    ]


def _sync_step(kind: str, *fields) -> bytes:
    """The bytes of a step of a sync: kind, slot, fork name and data."""
    match kind, fields:
        case "update", (fork, slot, data):
            code = 0
        case "force", (slot,):
            code, fork, data = 1, "", b""
        case "upgrade", (fork,):
            code, slot, data = 2, 0, b""
        case _:
            raise ValueError(f"no sync step {kind} {fields}")
    name = fork.encode()
    return (
        bytes([code])
        + slot.to_bytes(8, "little")
        + bytes([len(name)])
        + name
        + len(data).to_bytes(4, "little")
        + data
    )


def block_to_light_client_header(
    name: str, fork: str, block: bytes, config: dict | None = None
) -> tuple[bytes, bytes]:
    """The root of a signed block, and the SSZ bytes of its light client header."""
    replacements = json.dumps(config).encode() if config else b""
    out = _native.consensus_block_to_light_client_header(name, fork, replacements, block)
    return out[:32], out[32:]


def light_client_update_proofs(
    name: str, fork: str, type_name: str, data: bytes, config: dict | None = None
) -> bool:
    """Check the attested header and the branches of a light client update."""
    replacements = json.dumps(config).encode() if config else b""
    return _native.consensus_light_client_update_proofs(name, fork, type_name, replacements, data)


def is_better_update(
    name: str,
    fork: str,
    new_update: bytes,
    old_update: bytes,
    old_fork: str | None = None,
    config: dict | None = None,
) -> bool:
    """Whether a new light client update ranks above an old one, both at the later fork."""
    replacements = json.dumps(config).encode() if config else b""
    return _native.consensus_is_better_update(
        name, fork, old_fork or fork, replacements, new_update, old_update
    )


def genesis_block(name: str, fork: str, state: bytes) -> bytes:
    """The SSZ bytes of the genesis block of a state, signed with zero bytes."""
    return _native.consensus_genesis_block(name, fork, state)


def create_light_client_bootstrap(
    name: str, fork: str, state: bytes, block: bytes, config: dict | None = None
) -> bytes:
    """The SSZ bytes of the bootstrap that a full node serves for a block and its post state."""
    replacements = json.dumps(config).encode() if config else b""
    return _native.consensus_create_light_client_bootstrap(name, fork, replacements, state, block)


def create_light_client_update(
    name: str,
    fork: str,
    type_name: str,
    state: bytes,
    block: bytes,
    attested_state: bytes,
    attested_block: bytes,
    finalized_block: bytes | None,
    config: dict | None = None,
    attested_fork: str | None = None,
    finalized_fork: str | None = None,
) -> bytes:
    """The SSZ bytes of the update of a type that a full node serves for a block."""
    replacements = json.dumps(config).encode() if config else b""
    attested_fork = attested_fork or fork
    return _native.consensus_create_light_client_update(
        name,
        fork,
        attested_fork,
        finalized_fork or attested_fork,
        type_name,
        replacements,
        state,
        block,
        attested_state,
        attested_block,
        finalized_block or b"",
    )


def compute_fork_digest(
    name: str, genesis_validators_root: bytes, epoch: int, config: dict | None = None
) -> bytes:
    """The fork digest at an epoch, on the chain with the given root of the genesis validators."""
    replacements = json.dumps(config).encode() if config else b""
    return _native.consensus_compute_fork_digest(name, replacements, genesis_validators_root, epoch)


def compute_matrix(blobs: list) -> list:
    """The entries of the matrix of the blobs, each in its SSZ encoding."""
    out = _native.consensus_compute_matrix(b"".join(blobs))
    return [out[i : i + MATRIX_ENTRY_BYTES] for i in range(0, len(out), MATRIX_ENTRY_BYTES)]


def recover_matrix(entries: list, blob_count: int) -> list:
    """The entries of the full matrix of `blob_count` rows, recovered from some of its entries."""
    out = _native.consensus_recover_matrix(b"".join(entries), blob_count)
    return [out[i : i + MATRIX_ENTRY_BYTES] for i in range(0, len(out), MATRIX_ENTRY_BYTES)]


def get_data_column_sidecars_from_block(name: str, fork: str, block: bytes, rows: list) -> list:
    """The data column sidecars of a signed block, from the cells and proofs of each blob."""
    joined = b"".join(b"".join(cells) + b"".join(proofs) for cells, proofs in rows)
    return _list_items(
        _native.consensus_get_data_column_sidecars_from_block(name, fork, block, joined)
    )


def get_data_column_sidecars_from_column_sidecar(
    name: str, fork: str, sidecar: bytes, rows: list
) -> list:
    """All the data column sidecars of a block, from one of them and the cells of each blob."""
    joined = b"".join(b"".join(cells) + b"".join(proofs) for cells, proofs in rows)
    return _list_items(
        _native.consensus_get_data_column_sidecars_from_column_sidecar(name, fork, sidecar, joined)
    )


def process_operation(
    name: str,
    fork: str,
    handler: str,
    pre: bytes,
    operation: bytes,
    verify: bool = True,
    config: dict | None = None,
    execution_valid: bool = True,
) -> bytes:
    """The SSZ bytes of a beacon state after one block operation, or TransitionError."""
    replacements = json.dumps(config).encode() if config else b""
    return _native.consensus_process_operation(
        name, fork, handler, pre, operation, replacements, verify, execution_valid
    )


def process_epoch(
    name: str, fork: str, handler: str, pre: bytes, config: dict | None = None
) -> bytes:
    """The SSZ bytes of a beacon state after one epoch transition step, or TransitionError."""
    replacements = json.dumps(config).encode() if config else b""
    return _native.consensus_process_epoch(name, fork, handler, pre, replacements)


def rewards_deltas(
    name: str, fork: str, component: str, pre: bytes, config: dict | None = None
) -> bytes:
    """The SSZ bytes of the reward and penalty deltas of one kind of vote, or TransitionError."""
    replacements = json.dumps(config).encode() if config else b""
    return _native.consensus_rewards_deltas(name, fork, component, pre, replacements)


def process_slots(
    name: str, fork: str, pre: bytes, slots: int, config: dict | None = None
) -> bytes:
    """The SSZ bytes of a beacon state some slots later, or TransitionError."""
    replacements = json.dumps(config).encode() if config else b""
    return _native.consensus_process_slots(name, fork, pre, replacements, slots)


def state_transition(
    name: str, fork: str, pre: bytes, block: bytes, verify: bool = True, config: dict | None = None
) -> bytes:
    """The SSZ bytes of a beacon state after a signed block, or TransitionError."""
    replacements = json.dumps(config).encode() if config else b""
    return _native.consensus_state_transition(name, fork, pre, block, replacements, verify)


def state_transition_across(
    name: str,
    fork: str,
    pre: bytes,
    block_fork: str,
    block: bytes,
    verify: bool = True,
    config: dict | None = None,
) -> bytes:
    """The SSZ bytes of a state after a block of the same or a later fork, or TransitionError."""
    replacements = json.dumps(config).encode() if config else b""
    return _native.consensus_state_transition_across(
        name, fork, pre, block_fork, block, replacements, verify
    )


_FORK_CHOICE_STEPS = {
    "tick": 0,
    "block": 1,
    "attestation": 2,
    "attester_slashing": 3,
    "checks": 4,
    "pow_block": 5,
    "payload": 8,
    "fast_confirmation": 9,
    "execution_payload": 10,
    "payload_attestation_message": 11,
}

# The verdicts of the execution layer that find a payload invalid.
_INVALID_PAYLOAD = ("INVALID", "INVALID_BLOCK_HASH")


def fork_choice(
    name: str,
    fork: str,
    anchor_state: bytes,
    anchor_block: bytes,
    steps: list,
    verify: bool = True,
    config: dict | None = None,
) -> list:
    """The outcome of each step of a fork choice case, from an anchor state and block."""
    # A step is (kind, data): the tick in seconds, the SSZ bytes of a block, an attestation, an
    # attester slashing or a PoW block, or for "checks" what the read asks.
    # A read asks for the proposer head when its data is true.
    # It may also be (proposer head, viable leaves, root or None): the leaves of the filtered
    # tree with their weights, and the votes of the payload committee on the block of the root.
    # From Gloas an "execution_payload" step is a signed envelope, and a
    # "payload_attestation_message" step a vote of the payload committee, both in SSZ.
    # From Deneb a block may come as (block, blobs, proofs): the node holds those for it.
    # From Fulu a block may come as (block, columns): the node samples those SSZ columns for it,
    # and an empty list means that it cannot get them.
    # A "payload" step is (status, latest valid hash or None): the verdict of the execution
    # layer on the payload of the next block, by its Engine API name.
    # A "fast_confirmation" step, with data None, runs the fast confirmation of the slot.
    records = b""
    for kind, data in steps:
        if kind == "tick":
            data = data.to_bytes(8, "little")
        elif kind == "checks":
            proposer_head, viable, root = data if isinstance(data, tuple) else (data, False, None)
            flags = bool(proposer_head) | 2 * bool(viable) | 4 * (root is not None)
            data = bytes([flags]) + (root or b"")
        elif kind == "fast_confirmation":
            data = b""
        elif kind == "payload":
            status, latest_valid_hash = data
            invalid = status in _INVALID_PAYLOAD
            data = bytes([invalid]) + (latest_valid_hash or b"" if invalid else b"")
        elif kind == "block" and isinstance(data, tuple) and len(data) == 3:
            data, blobs, proofs = data
            held = len(blobs).to_bytes(4, "little") + b"".join(blobs) + b"".join(proofs)
            records += bytes([6]) + len(held).to_bytes(4, "little") + held
        elif kind == "block" and isinstance(data, tuple):
            data, columns = data
            held = len(columns).to_bytes(4, "little") + b"".join(
                len(column).to_bytes(4, "little") + column for column in columns
            )
            records += bytes([7]) + len(held).to_bytes(4, "little") + held
        records += bytes([_FORK_CHOICE_STEPS[kind]]) + len(data).to_bytes(4, "little") + data
    replacements = json.dumps(config).encode() if config else b""
    out = _native.consensus_fork_choice(
        name, fork, anchor_state, anchor_block, records, replacements, verify
    )
    outcomes, offset = [], 0
    for kind, data in steps:
        if kind == "block" and isinstance(data, tuple):
            # The blobs or the columns that the node holds take no part in the outcome.
            offset += 1
        status, offset = out[offset], offset + 1
        if status == 1:
            code = int.from_bytes(out[offset : offset + 4], "little")
            length = int.from_bytes(out[offset + 4 : offset + 8], "little")
            message = out[offset + 8 : offset + 8 + length].decode()
            outcomes.append(ForkChoiceError(code, message))
            offset += 8 + length
        elif kind == "fast_confirmation":
            size = 216 + 1 + 32 * out[offset + 216]
            outcomes.append(_fast_confirmation_record(out[offset : offset + size]))
            offset += size
        elif kind != "checks":
            outcomes.append(None)
        else:
            read, offset = _store_record(out, offset, data)
            outcomes.append(read)
    return outcomes


def gossip_validation(
    name: str,
    fork: str,
    anchor_state: bytes,
    anchor_block: bytes,
    topic: str,
    messages: list[tuple[int, int, bytes]],
    verify: bool = True,
    config: dict | None = None,
    blocks: list[tuple[int, int | None, bytes]] | None = None,
    finalized: tuple[int, bytes] | None = None,
) -> list[tuple[str, str | None]]:
    """The outcome of each gossip message of a topic, in turn, with the reason of a failure."""
    # A block after the anchor is (1 if failed, 2 if pending, else 0; payload status; SSZ bytes).
    block_records = b"".join(
        bytes([kind, 255 if status is None else status]) + len(data).to_bytes(4, "little") + data
        for kind, status, data in blocks or []
    )
    checkpoint = b"" if finalized is None else finalized[0].to_bytes(8, "little") + finalized[1]
    # A message is (arrival time in milliseconds, subnet ID, SSZ bytes).
    records = b"".join(
        time.to_bytes(8, "little")
        + subnet.to_bytes(8, "little")
        + len(data).to_bytes(4, "little")
        + data
        for time, subnet, data in messages
    )
    replacements = json.dumps(config).encode() if config else b""
    out = _native.consensus_gossip_validation(
        name,
        fork,
        anchor_state,
        anchor_block,
        block_records,
        checkpoint,
        topic.encode(),
        records,
        replacements,
        verify,
    )
    outcomes, offset = [], 0
    while offset < len(out):
        status, offset = out[offset], offset + 1
        if status == 0:
            outcomes.append(("valid", None))
            continue
        length = int.from_bytes(out[offset : offset + 4], "little")
        reason = out[offset + 4 : offset + 4 + length].decode()
        outcomes.append(("ignore" if status == 1 else "reject", reason))
        offset += 4 + length
    return outcomes


def _store_record(out: bytes, offset: int, asked) -> tuple[dict, int]:
    """A read of the store from its bytes at an offset, and the offset after it."""
    proposer_head, viable, root = asked if isinstance(asked, tuple) else (asked, False, None)
    record = out[offset:]

    def number(start: int, width: int = 8) -> int:
        return int.from_bytes(record[start : start + width], "little")

    def checkpoint(start: int) -> dict:
        return {"epoch": number(start), "root": record[start + 8 : start + 40]}

    read = {
        "head": {"slot": number(0), "root": record[8:40]},
        "time_ms": number(40),
        "genesis_time_ms": number(48),
        "justified_checkpoint": checkpoint(56),
        "finalized_checkpoint": checkpoint(96),
        "proposer_boost_root": record[136:168],
    }
    at = 168
    if proposer_head:
        read["proposer_head"] = record[at : at + 32]
        at += 32
    read["head"]["payload_status"] = record[at]
    at += 1
    if viable:
        count, at = number(at, 4), at + 4
        read["viable_for_head_roots_and_weights"] = [
            {
                "root": record[at + 41 * i : at + 41 * i + 32],
                "weight": number(at + 41 * i + 32),
                "payload_status": record[at + 41 * i + 40],
            }
            for i in range(count)
        ]
        at += 41 * count
    if root is not None:
        # Each vote is a byte: 0 false, 1 true, 2 none.
        size, at = number(at, 4), at + 4
        votes = [None if vote == 2 else bool(vote) for vote in record[at : at + 2 * size]]
        read["payload_timeliness_vote"] = votes[:size]
        read["payload_data_availability_vote"] = votes[size:]
        at += 2 * size
    return read, offset + at


def _fast_confirmation_record(record: bytes) -> dict:
    """A read of the fast confirmation store, from its bytes."""

    def checkpoint(start: int) -> dict:
        return {
            "epoch": int.from_bytes(record[start : start + 8], "little"),
            "root": record[start + 8 : start + 40],
        }

    read = {
        "previous_epoch_observed_justified_checkpoint": checkpoint(0),
        "current_epoch_observed_justified_checkpoint": checkpoint(40),
        "previous_epoch_greatest_unrealized_checkpoint": checkpoint(80),
        "previous_slot_head": record[120:152],
        "current_slot_head": record[152:184],
        "confirmed_root": record[184:216],
    }
    if record[216]:
        read["safe_execution_block_hash"] = record[217:249]
    return read


def initialize_genesis(
    name: str,
    fork: str,
    eth1_block_hash: bytes,
    eth1_timestamp: int,
    deposits: list[bytes],
    verify: bool = True,
    config: dict | None = None,
) -> bytes:
    """The SSZ bytes of the candidate genesis state of a block and its deposits."""
    replacements = json.dumps(config).encode() if config else b""
    return _native.consensus_initialize_genesis(
        name, fork, eth1_block_hash, b"".join(deposits), replacements, eth1_timestamp, verify
    )


def is_valid_genesis_state(name: str, fork: str, state: bytes, config: dict | None = None) -> bool:
    """Whether a candidate genesis state launches the chain."""
    replacements = json.dumps(config).encode() if config else b""
    return _native.consensus_is_valid_genesis_state(name, fork, state, replacements)


def compute_weak_subjectivity_period(
    name: str, fork: str, state: bytes, config: dict | None = None
) -> int:
    """The weak subjectivity period of a state, in epochs, or WeakSubjectivityError."""
    replacements = json.dumps(config).encode() if config else b""
    return _native.consensus_compute_weak_subjectivity_period(name, fork, state, replacements)


def is_within_weak_subjectivity_period(
    name: str,
    fork: str,
    ws_state: bytes,
    ws_checkpoint: bytes,
    genesis_time_ms: int,
    time_ms: int,
    config: dict | None = None,
) -> bool:
    """Whether a checkpoint and its state are within the period at the two times of a store."""
    replacements = json.dumps(config).encode() if config else b""
    return _native.consensus_is_within_weak_subjectivity_period(
        name, fork, ws_state, ws_checkpoint, replacements, genesis_time_ms, time_ms
    )


def _replacements(config: dict | None) -> bytes:
    return json.dumps(config).encode() if config else b""


def get_committee_assignment(
    name: str, fork: str, state: bytes, epoch: int, validator_index: int, config: dict | None = None
) -> tuple[list, int, int] | None:
    """The committee, its index and its slot for a validator in an epoch, or None."""
    out = json.loads(
        _native.consensus_get_committee_assignment(
            name, fork, state, _replacements(config), epoch, validator_index
        )
    )
    return None if out is None else (out["committee"], out["index"], out["slot"])


def is_proposer(
    name: str, fork: str, state: bytes, validator_index: int, config: dict | None = None
) -> bool:
    """Whether a validator proposes the block of the slot of a state."""
    return _native.consensus_is_proposer(name, fork, state, _replacements(config), validator_index)


def is_assigned_to_sync_committee(
    name: str, fork: str, state: bytes, epoch: int, validator_index: int, config: dict | None = None
) -> bool:
    """Whether a validator serves on the sync committee of the period of an epoch."""
    return _native.consensus_is_assigned_to_sync_committee(
        name, fork, state, _replacements(config), epoch, validator_index
    )


def compute_subnets_for_sync_committee(
    name: str, fork: str, state: bytes, validator_index: int, config: dict | None = None
) -> list:
    """The sync committee subnets of a validator for the next slot, in increasing order."""
    return json.loads(
        _native.consensus_compute_subnets_for_sync_committee(
            name, fork, state, _replacements(config), validator_index
        )
    )


def get_ptc_assignment(
    name: str, fork: str, state: bytes, epoch: int, validator_index: int, config: dict | None = None
) -> int | None:
    """The slot of an epoch whose payload timeliness committee holds a validator, or None."""
    return json.loads(
        _native.consensus_get_ptc_assignment(
            name, fork, state, _replacements(config), epoch, validator_index
        )
    )


def get_upcoming_proposal_slots(
    name: str, fork: str, state: bytes, validator_index: int, config: dict | None = None
) -> list:
    """The slots after the slot of a state that a validator proposes, in increasing order."""
    return json.loads(
        _native.consensus_get_upcoming_proposal_slots(
            name, fork, state, _replacements(config), validator_index
        )
    )


def get_validator_signature(
    name: str,
    fork: str,
    state: bytes,
    duty: str,
    obj: bytes,
    secret_key: bytes,
    config: dict | None = None,
) -> bytes:
    """The 96-byte signature of the SSZ bytes of the object of a duty, by a secret key."""
    return _native.consensus_get_validator_signature(
        name, fork, state, _replacements(config), duty, obj, secret_key
    )


def get_eth1_vote(
    name: str, fork: str, state: bytes, chain: list, config: dict | None = None
) -> bytes:
    """The Eth1 data that a proposer votes for, from Eth1 blocks as (timestamp, Eth1 data)."""
    blocks = [struct.pack("<Q", timestamp) + data for timestamp, data in chain]
    return _native.consensus_get_eth1_vote(name, fork, state, _replacements(config), blocks)


def get_eth1_pending_deposit_count(name: str, fork: str, state: bytes) -> int:
    """In Electra, the number of deposits of the deposit contract that a block holds."""
    return _native.consensus_get_eth1_pending_deposit_count(name, fork, state)


def compute_new_state_root(
    name: str,
    fork: str,
    state: bytes,
    block: bytes,
    verify: bool = True,
    config: dict | None = None,
) -> bytes:
    """The 32-byte root of the state after a block, to set as the state root of that block."""
    return _native.consensus_compute_new_state_root(
        name, fork, state, block, _replacements(config), verify
    )


def compute_on_chain_aggregate(name: str, fork: str, aggregates: list) -> bytes:
    """The attestation on chain from network aggregates of the same data, as SSZ bytes."""
    return _native.consensus_compute_on_chain_aggregate(name, fork, aggregates)


def get_execution_requests(name: str, fork: str, requests: list) -> bytes:
    """The requests of an execution block from the typed lists of the execution layer."""
    return _native.consensus_get_execution_requests(name, fork, requests)


def get_validators_custody_requirement(
    name: str, fork: str, state: bytes, validator_indices: list, config: dict | None = None
) -> int:
    """The number of custody groups of a node with these validators."""
    indices = [struct.pack("<Q", index) for index in validator_indices]
    return _native.consensus_get_validators_custody_requirement(
        name, fork, state, _replacements(config), indices
    )


def upgrade_state(
    name: str, fork: str, pre: bytes, verify: bool = True, config: dict | None = None
) -> bytes:
    """The SSZ bytes of a state upgraded to a fork from the fork before, or TransitionError."""
    replacements = json.dumps(config).encode() if config else b""
    return _native.consensus_upgrade_state(name, fork, pre, replacements, verify)


__all__ = [
    "preset",
    "config",
    "parameters",
    "ConsensusError",
    "get_custody_groups",
    "compute_columns_for_custody_group",
    "ssz_static",
    "pq_keys_ssz",
    "pq_keys_possession_signing_root",
    "pq_keys_is_valid_possession_proof",
    "compute_shuffled_permutation",
    "compute_shuffled_index",
    "reqresp_protocol_ids",
    "reqresp_parse_protocol_id",
    "reqresp_message",
    "compute_min_epochs_for_block_requests",
    "gossip_topics",
    "compute_subnet_for_attestation",
    "compute_subnet_for_blob_sidecar",
    "compute_subnet_for_data_column_sidecar",
    "compute_subscribed_subnets",
    "merkle_proof",
    "verify_blob_sidecar_inclusion_proof",
    "verify_data_column_sidecar",
    "verify_data_column_sidecar_inclusion_proof",
    "verify_data_column_sidecar_kzg_proofs",
    "verify_partial_data_column_header_inclusion_proof",
    "verify_partial_data_column_sidecar_kzg_proofs",
    "compute_matrix",
    "recover_matrix",
    "get_data_column_sidecars_from_block",
    "get_data_column_sidecars_from_column_sidecar",
    "TransitionError",
    "WeakSubjectivityError",
    "ValidatorDutyError",
    "ProposerError",
    "process_operation",
    "LightClientError",
    "ForkChoiceError",
    "fork_choice",
    "gossip_validation",
    "light_client_sync",
    "block_to_light_client_header",
    "light_client_update_proofs",
    "is_better_update",
    "genesis_block",
    "create_light_client_bootstrap",
    "create_light_client_update",
    "compute_fork_digest",
    "process_epoch",
    "rewards_deltas",
    "upgrade_state",
    "compute_weak_subjectivity_period",
    "is_within_weak_subjectivity_period",
    "get_committee_assignment",
    "is_proposer",
    "is_assigned_to_sync_committee",
    "compute_subnets_for_sync_committee",
    "get_ptc_assignment",
    "get_upcoming_proposal_slots",
    "get_validator_signature",
    "get_eth1_vote",
    "get_eth1_pending_deposit_count",
    "compute_new_state_root",
    "compute_on_chain_aggregate",
    "get_execution_requests",
    "get_validators_custody_requirement",
    "process_slots",
    "state_transition",
    "state_transition_across",
]
