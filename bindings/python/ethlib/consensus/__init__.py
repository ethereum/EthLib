"""The consensus layer: presets, configurations, containers, the shuffle, custody and networking."""

from collections.abc import Sequence
from typing import Any, Literal, TypeAlias

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import (
    ConsensusError,
    DepositTreeError,
    ForkChoiceError,
    LightClientError,
    ProposerError,
    SlashingProtectionError,
    TransitionError,
    ValidatorDutyError,
    WeakSubjectivityError,
)


def preset(name: str) -> dict[str, int]:
    """The values of a preset, with the values that it derives from them."""
    return _native.consensus_preset(name)


def config(name: str) -> dict[str, Any]:
    """The values of a configuration."""
    # A value is an int, a str such as 0x and hex, or a list of dicts for a schedule.
    return _native.consensus_config(name)


def parameters(name: str, fork: str) -> dict[str, int]:
    """The values of a preset that a fork replaces, as they stand at the fork."""
    return _native.consensus_parameters(name, fork)


def get_custody_groups(node_id: int, custody_group_count: int, name: str = "mainnet") -> list[int]:
    """The sorted custody groups of a node, or ConsensusError when they cannot be selected."""
    return _native.consensus_get_custody_groups(name, node_id, custody_group_count)


def compute_columns_for_custody_group(custody_group: int, name: str = "mainnet") -> list[int]:
    """The columns of a custody group, or ConsensusError for a group out of range."""
    return _native.consensus_compute_columns_for_custody_group(name, custody_group)


def get_custody_column_bits(node_id: int, custody_group_count: int, name: str = "mainnet") -> bytes:
    """The SSZ bitvector of the columns that a node custodies, or ConsensusError."""
    return _native.consensus_get_custody_column_bits(name, node_id, custody_group_count)


def ssz_static(name: str, fork: str, type_name: str, data: bytes) -> tuple[bytes, bytes]:
    """The root of the beacon container that SSZ bytes encode, and its bytes encoded again."""
    return _native.consensus_ssz_static(name, fork, type_name, data)


def api_json(name: str, fork: str, type_name: str, data: bytes) -> dict[str, Any]:
    """The Beacon API JSON of the beacon container that SSZ bytes encode, or SszError."""
    # A value is a dict, a list, a str or a bool, nested as the container is.
    # The values are `Any`, so that a caller indexes nested values without narrowing them.
    # The order of the keys of a dict carries no meaning.
    return _native.consensus_api_json(name, fork, type_name, data)


def api_ssz(name: str, fork: str, type_name: str, document: object) -> bytes:
    """The SSZ bytes of the container that a Beacon API JSON document holds, or SszError."""
    # A value that the bindings cannot pass to Lean, such as a float, raises TypeError.
    # A negative or too large int, a nesting deeper than 64, or too many parts raise ValueError.
    return _native.consensus_api_ssz(name, fork, type_name, document)


def builder_api_json(name: str, fork: str, type_name: str, data: bytes) -> dict[str, Any]:
    """The versioned Builder API body of the container that SSZ bytes encode, or SszError."""
    return _native.consensus_builder_api_json(name, fork, type_name, data)


def builder_api_ssz(name: str, fork: str, type_name: str, document: object) -> bytes:
    """The SSZ bytes of the container in a Builder API response body of the fork, or SszError."""
    return _native.consensus_builder_api_ssz(name, fork, type_name, document)


def is_valid_builder_signature(
    name: str,
    fork: str,
    type_name: str,
    data: bytes,
    # `Any`, because `dict` is invariant in its values.
    config: dict[str, Any] | None = None,
) -> bool:
    """Whether a signed registration or bid of the Builder API verifies."""
    return _native.consensus_is_valid_builder_signature(name, fork, config, type_name, data)


def process_registration(
    name: str,
    fork: str,
    state: bytes,
    registry: list[bytes],
    signed: bytes,
    now: int,
    # `Any`, because `dict` is invariant in its values.
    config: dict[str, Any] | None = None,
) -> str | None:
    """None when a builder keeps a signed registration, or the name of the rule that refuses it."""
    return _native.consensus_process_registration(name, fork, config, state, registry, signed, now)


def is_eligible_for_bid(
    name: str,
    fork: str,
    state: bytes,
    registry: list[bytes],
    slot: int,
    parent_hash: bytes,
    pubkey: bytes,
) -> bool:
    """Whether a builder serves a request for a bid, given its signed registrations."""
    return _native.consensus_is_eligible_for_bid(
        name, fork, state, registry, slot, parent_hash, pubkey
    )


def process_bid(
    name: str,
    fork: str,
    state: bytes,
    signed: bytes,
    fee_recipient: bytes,
    # `Any`, because `dict` is invariant in its values.
    config: dict[str, Any] | None = None,
) -> str | None:
    """None when a proposer accepts a signed bid, or the name of the rule that refuses it."""
    return _native.consensus_process_bid(name, fork, config, state, signed, fee_recipient)


def is_eligible_for_bid_gloas(
    name: str,
    fork: str,
    state: bytes,
    preferences: list[bytes],
    slot: int,
    parent_hash: bytes,
    parent_root: bytes,
    pubkey: bytes,
) -> bool:
    """From Gloas: whether a builder serves a request for a bid, or TransitionError."""
    return _native.consensus_is_eligible_for_bid_gloas(
        name, fork, state, preferences, slot, parent_hash, parent_root, pubkey
    )


def validate_bid(
    name: str,
    fork: str,
    state: bytes,
    preferences: bytes,
    parent_gas_limit: int,
    signed: bytes,
    fee_recipient: bytes,
    # `Any`, because `dict` is invariant in its values.
    config: dict[str, Any] | None = None,
) -> str | None:
    """From Gloas: None when a proposer accepts a bid, the rule refusing it, or TransitionError."""
    return _native.consensus_validate_bid(
        name, fork, config, state, preferences, parent_gas_limit, signed, fee_recipient
    )


def unblind_signed_blinded_block(
    name: str, fork: str, blinded: bytes, revealed: bytes
) -> tuple[bytes, bytes] | None:
    """The root and bytes of the signed block that a signed blinded block and a payload give."""
    return _native.consensus_unblind_signed_blinded_block(name, fork, blinded, revealed)


def verify_builder_request_auth_signature(
    name: str,
    fork: str,
    pubkey: bytes,
    data: bytes,
    # `Any`, because `dict` is invariant in its values.
    config: dict[str, Any] | None = None,
) -> bool:
    """Whether the proposer key signed a Gloas request authentication; data and slot unchecked."""
    return _native.consensus_verify_builder_request_auth_signature(name, fork, config, pubkey, data)


def builder_request_auth_failures(
    name: str,
    fork: str,
    agreed: bytes,
    path_slot: int,
    pubkey: bytes,
    version_header: str | None,
    data: bytes,
    # `Any`, because `dict` is invariant in its values.
    config: dict[str, Any] | None = None,
) -> list[str]:
    """The names of the checks that fail on a Gloas request for a bid, in order."""
    return _native.consensus_builder_request_auth_failures(
        name, fork, config, agreed, path_slot, pubkey, version_header, data
    )


def builder_preferences_failures(
    name: str,
    fork: str,
    agreed: bytes,
    current_slot: int,
    pubkey: bytes,
    version_header: str | None,
    data: bytes,
    # `Any`, because `dict` is invariant in its values.
    config: dict[str, Any] | None = None,
) -> list[str]:
    """The names of the checks that fail on a Gloas request that submits preferences, in order."""
    return _native.consensus_builder_preferences_failures(
        name, fork, config, agreed, current_slot, pubkey, version_header, data
    )


def default_auth_data(url: str) -> bytes:
    """From Gloas: a builder's default auth data, its URL's host lowercased, IPv6 compressed."""
    return _native.consensus_default_auth_data(url)


def relay_submission_bid(name: str, fork: str, data: bytes, pubkey: bytes) -> bytes:
    """The SSZ bytes of the bid that a relay serves from an SSZ block submission, with the key."""
    return _native.consensus_relay_submission_bid(name, fork, data, pubkey)


def relay_validators(
    name: str, fork: str, state: bytes, registry: list[bytes]
) -> list[dict[str, Any]]:
    """At Fulu only: the JSON entries of the validators that a relay lists, from SSZ bytes."""
    return _native.consensus_relay_validators(name, fork, state, registry)


def relay_delivered_payload(document: dict[str, Any]) -> dict[str, Any]:
    """A delivered payload of the relay data API, checked and written back as canonical JSON."""
    return _native.consensus_relay_delivered_payload(document)


def relay_received_bid(document: dict[str, Any]) -> dict[str, Any]:
    """A received bid of the relay data API, checked and written back as canonical JSON."""
    return _native.consensus_relay_received_bid(document)


def relay_delivered_keeps(
    document: dict[str, Any],
    *,
    slot: int | None = None,
    block_hash: bytes | None = None,
    block_number: int | None = None,
    proposer_pubkey: bytes | None = None,
    builder_pubkey: bytes | None = None,
) -> bool:
    """Whether a query of delivered payloads with these filters keeps the payload."""
    return _native.consensus_relay_delivered_keeps(
        document, slot, block_hash, block_number, proposer_pubkey, builder_pubkey
    )


def relay_received_keeps(
    document: dict[str, Any],
    *,
    slot: int | None = None,
    block_hash: bytes | None = None,
    block_number: int | None = None,
    builder_pubkey: bytes | None = None,
) -> bool:
    """Whether a query of received bids with these filters keeps the bid."""
    return _native.consensus_relay_received_keeps(
        document, slot, block_hash, block_number, builder_pubkey
    )


def relay_sort_delivered(
    order: Literal["value", "-value"], documents: list[dict[str, Any]]
) -> list[dict[str, Any]]:
    """Delivered payloads sorted by value in an order; payloads of equal value keep their order."""
    return _native.consensus_relay_sort_delivered(order, documents)


def builder_bid_value(value: int, execution_payment: int, max_execution_payment: int) -> int:
    """The bid's value in Gwei, with its execution payment capped, not reduced to 64 bits."""
    return _native.consensus_builder_bid_value(value, execution_payment, max_execution_payment)


def consensus_version(fork: str) -> str | None:
    """The Beacon API name of a fork's consensus version, or None before Phase 0 and at Hegotá."""
    return _native.consensus_consensus_version(fork)


def consensus_version_fork(name: str) -> str:
    """The first fork of the consensus version with this exact Beacon API name."""
    return _native.consensus_consensus_version_fork(name)


def upgrade_operation(name: str, type_name: str, data: bytes) -> tuple[bytes, bytes]:
    """The Gloas root and bytes of a Fulu attestation, indexed attestation or attester slashing."""
    return _native.consensus_upgrade_operation(name, type_name, data)


def pq_keys_ssz(type_name: str, data: bytes) -> tuple[bytes, bytes]:
    """The root of the EIP-8450 container that SSZ bytes encode, and its bytes encoded again."""
    return _native.pq_keys_ssz(type_name, data)


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


def compute_shuffled_permutation(count: int, seed: bytes, name: str = "mainnet") -> list[int]:
    """The shuffled position of every index below the count."""
    return _native.consensus_compute_shuffled_permutation(name, count, seed)


def compute_shuffled_index(index: int, count: int, seed: bytes, name: str = "mainnet") -> int:
    """The shuffled position of one index, or ConsensusError when it is not below the count."""
    return _native.consensus_compute_shuffled_index(name, index, count, seed)


def reqresp_protocol_ids(fork: str) -> list[str]:
    """The request and response protocol IDs of a fork."""
    return _native.consensus_reqresp_protocol_ids(fork)


def reqresp_parse_protocol_id(text: str) -> tuple[str, int]:
    """The protocol name and the version that a protocol ID names."""
    return _native.consensus_reqresp_parse_protocol_id(text)


def reqresp_message(name: str, fork: str, type_name: str, data: bytes) -> tuple[bytes, bytes]:
    """The root of a req/resp message that SSZ bytes encode, and its bytes encoded again."""
    return _native.consensus_reqresp_message(name, fork, type_name, data)


def compute_min_epochs_for_block_requests(fork: str, name: str = "mainnet") -> int:
    """The fewest epochs back from the current one that a node must serve blocks for, at a fork."""
    return _native.consensus_compute_min_epochs_for_block_requests(name, fork)


def gossip_topics(fork: str, name: str = "mainnet") -> list[str]:
    """The names of the gossip topics of a fork."""
    return _native.consensus_gossip_topics(name, fork)


def reqresp_request_bounds(fork: str, protocol: str, name: str = "mainnet") -> tuple[int, int]:
    """The smallest and the largest length of the request payload of a protocol ID at a fork."""
    return _native.consensus_reqresp_request_bounds(name, fork, protocol)


def reqresp_response_bounds(
    chunk_fork: str, protocol: str, name: str = "mainnet"
) -> tuple[int, int]:
    """The smallest and the largest length of a successful response chunk at its fork."""
    return _native.consensus_reqresp_response_bounds(name, chunk_fork, protocol)


# What a response check reads from each item, field by field.
# A block: its slot, the root of its parent and its own root.
ResponseBlock: TypeAlias = tuple[int, bytes, bytes]
# A blob or column sidecar: the slot and root of its block, and its index.
ResponseSidecar: TypeAlias = tuple[int, bytes, int]
# A payload envelope: its slot, its block root, the parent hash and the block hash of its payload.
ResponseEnvelope: TypeAlias = tuple[int, bytes, bytes, bytes]
# An inclusion list: its slot, its validator index and its dependent root.
ResponseInclusionList: TypeAlias = tuple[int, int, bytes]
ResponseItems: TypeAlias = (
    Sequence[ResponseBlock]
    | Sequence[ResponseSidecar]
    | Sequence[ResponseEnvelope]
    | Sequence[ResponseInclusionList]
)


def reqresp_is_valid_response(
    fork: str,
    protocol: str,
    request: bytes,
    items: ResponseItems,
    committee: Sequence[int] = (),
    name: str = "mainnet",
) -> bool:
    """Whether the items of a response are valid for the SSZ request of a protocol ID at a fork."""
    # The committee counts only for inclusion lists, as the validator of each seat.
    native_items: list[tuple[int | bytes, ...]] = list(items)
    return _native.consensus_reqresp_response_valid(
        name, fork, protocol, request, native_items, list(committee)
    )


def gossip_topic_bound(fork: str, topic: str, name: str = "mainnet") -> int:
    """The largest payload length of a gossip topic at a fork."""
    return _native.consensus_gossip_topic_bound(name, fork, topic)


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


def compute_subscribed_subnets(node_id: int, epoch: int, name: str = "mainnet") -> list[int]:
    """The attestation subnets of a node in an epoch."""
    return _native.consensus_compute_subscribed_subnets(name, node_id, epoch)


def merkle_proof(
    name: str, fork: str, type_name: str, data: bytes, gindex: int
) -> tuple[bytes, list[bytes]]:
    """The node at a generalized index of a beacon container, and its branch up to the root."""
    return _native.consensus_merkle_proof(name, fork, type_name, data, gindex)


def verify_blob_sidecar_inclusion_proof(name: str, fork: str, data: bytes) -> bool:
    """Whether the branch of a blob sidecar climbs from its commitment to its body root."""
    return _native.consensus_verify_blob_sidecar_inclusion_proof(name, fork, data)


def verify_data_column_sidecar(
    name: str,
    fork: str,
    data: bytes,
    block: bytes = b"",
    config: dict[str, Any] | None = None,
) -> bool:
    """Whether a data column sidecar has a valid shape; from Gloas, against its signed block."""
    return _native.consensus_verify_data_column_sidecar(name, fork, data, block, config)


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


# A step of a light client sync: an update of a fork at a slot, a forced update, or an upgrade.
SyncStep: TypeAlias = (
    tuple[Literal["update"], str, int, bytes]
    | tuple[Literal["force"], int]
    | tuple[Literal["upgrade"], str]
)

# A header after a step of a sync: its slot, its beacon root and its execution root.
SyncHeader: TypeAlias = tuple[int, bytes, bytes]


def light_client_sync(
    name: str,
    fork: str,
    bootstrap_fork: str,
    trusted_block_root: bytes,
    genesis_validators_root: bytes,
    bootstrap: bytes,
    steps: Sequence[SyncStep],
    config: dict[str, Any] | None = None,
) -> list[tuple[SyncHeader, SyncHeader]]:
    """The finalized and optimistic headers, as slot and two roots, after each step of a sync."""
    return _native.consensus_light_client_sync(
        name,
        fork,
        bootstrap_fork,
        config,
        trusted_block_root,
        genesis_validators_root,
        bootstrap,
        # A step read from JSON or YAML may be a list, which the converter reads as a tuple.
        [tuple(step) for step in steps],
    )


def block_to_light_client_header(
    name: str, fork: str, block: bytes, config: dict[str, Any] | None = None
) -> tuple[bytes, bytes]:
    """The root of a signed block, and the SSZ bytes of its light client header."""
    return _native.consensus_block_to_light_client_header(name, fork, config, block)


def light_client_update_proofs(
    name: str, fork: str, type_name: str, data: bytes, config: dict[str, Any] | None = None
) -> bool:
    """Check the attested header and the branches of a light client update."""
    return _native.consensus_light_client_update_proofs(name, fork, type_name, config, data)


def is_better_update(
    name: str,
    fork: str,
    new_update: bytes,
    old_update: bytes,
    old_fork: str | None = None,
    config: dict[str, Any] | None = None,
) -> bool:
    """Whether a new light client update ranks above an old one, both at the later fork."""
    return _native.consensus_is_better_update(
        name, fork, old_fork or fork, config, new_update, old_update
    )


def genesis_block(name: str, fork: str, state: bytes) -> bytes:
    """The SSZ bytes of the genesis block of a state, signed with zero bytes."""
    return _native.consensus_genesis_block(name, fork, state)


def create_light_client_bootstrap(
    name: str, fork: str, state: bytes, block: bytes, config: dict[str, Any] | None = None
) -> bytes:
    """The SSZ bytes of the bootstrap that a full node serves for a block and its post state."""
    return _native.consensus_create_light_client_bootstrap(name, fork, config, state, block)


def create_light_client_update(
    name: str,
    fork: str,
    type_name: str,
    state: bytes,
    block: bytes,
    attested_state: bytes,
    attested_block: bytes,
    finalized_block: bytes | None,
    config: dict[str, Any] | None = None,
    attested_fork: str | None = None,
    finalized_fork: str | None = None,
) -> bytes:
    """The SSZ bytes of the update of a type that a full node serves for a block."""
    attested_fork = attested_fork or fork
    return _native.consensus_create_light_client_update(
        name,
        fork,
        attested_fork,
        finalized_fork or attested_fork,
        type_name,
        config,
        state,
        block,
        attested_state,
        attested_block,
        finalized_block or None,
    )


# The light client containers that a light client update gives.
UpdateType: TypeAlias = Literal[
    "LightClientUpdate", "LightClientFinalityUpdate", "LightClientOptimisticUpdate"
]


def light_client_update_as(name: str, fork: str, type_name: UpdateType, update: bytes) -> bytes:
    """The SSZ bytes of a light client update, or of its finality or optimistic update."""
    return _native.consensus_light_client_update_as(name, fork, type_name, update)


# The outcome of a gossip message: valid with no reason, or ignore or reject with its reason.
GossipOutcome: TypeAlias = tuple[Literal["valid"], None] | tuple[Literal["ignore", "reject"], str]


def light_client_gossip_full_node(
    name: str,
    fork: str,
    genesis_time_ms: int,
    messages: Sequence[tuple[str, int, bytes, bytes | None]],
    config: dict[str, Any] | None = None,
) -> list[GossipOutcome]:
    """The outcome of each light client update on gossip at a full node, in turn."""
    # A message is (topic, arrival time in ms, SSZ bytes, the node's latest update or None).
    return _native.consensus_light_client_gossip_full_node(
        name, fork, config, genesis_time_ms, list(messages)
    )


def light_client_gossip_light_client(
    name: str,
    fork: str,
    genesis_time_ms: int,
    trusted_block_root: bytes,
    genesis_validators_root: bytes,
    bootstrap: bytes,
    messages: Sequence[tuple[str, int, bytes]],
    verify: bool = True,
    config: dict[str, Any] | None = None,
) -> list[GossipOutcome]:
    """The outcome of each light client update on gossip at a light client, in turn."""
    # A message is (topic, arrival time in milliseconds, SSZ bytes).
    # The store starts from the bootstrap and processes every update, whatever its outcome.
    return _native.consensus_light_client_gossip_light_client(
        name,
        fork,
        config,
        genesis_time_ms,
        trusted_block_root,
        genesis_validators_root,
        bootstrap,
        verify,
        list(messages),
    )


def compute_fork_digest(
    name: str, genesis_validators_root: bytes, epoch: int, config: dict[str, Any] | None = None
) -> bytes:
    """The fork digest at an epoch, on the chain with the given root of the genesis validators."""
    return _native.consensus_compute_fork_digest(name, config, genesis_validators_root, epoch)


def digest_epochs(name: str, config: dict[str, Any] | None = None) -> list[int]:
    """The epochs at which the fork digest can change, in increasing order and without repeats."""
    return _native.consensus_digest_epochs(name, config)


def fork_of_digest(
    name: str, genesis_validators_root: bytes, digest: bytes, config: dict[str, Any] | None = None
) -> tuple[int, str] | None:
    """The first epoch with the given digest, among those at which it can change, with its fork."""
    return _native.consensus_fork_of_digest(name, config, genesis_validators_root, digest)


def digests_identify(
    name: str, genesis_validators_root: bytes, config: dict[str, Any] | None = None
) -> bool:
    """Whether the digest of each epoch at which it can change reads back the fork at that epoch."""
    return _native.consensus_digests_identify(name, config, genesis_validators_root)


def compute_matrix(blobs: Sequence[bytes]) -> list[bytes]:
    """The entries of the matrix of the blobs, each in its SSZ encoding."""
    return _native.consensus_compute_matrix(list(blobs))


def recover_matrix(entries: Sequence[bytes], blob_count: int) -> list[bytes]:
    """The entries of the full matrix of `blob_count` rows, recovered from some of its entries."""
    return _native.consensus_recover_matrix(list(entries), blob_count)


# The cells of an extended blob and their proofs.
CellsAndProofs: TypeAlias = tuple[Sequence[bytes], Sequence[bytes]]


def get_data_column_sidecars_from_block(
    name: str, fork: str, block: bytes, rows: Sequence[CellsAndProofs]
) -> list[bytes]:
    """The data column sidecars of a signed block, from the cells and proofs of each blob."""
    return _native.consensus_get_data_column_sidecars_from_block(name, fork, block, _rows(rows))


def get_data_column_sidecars_from_column_sidecar(
    name: str, fork: str, sidecar: bytes, rows: Sequence[CellsAndProofs]
) -> list[bytes]:
    """All the data column sidecars of a block, from one of them and the cells of each blob."""
    return _native.consensus_get_data_column_sidecars_from_column_sidecar(
        name, fork, sidecar, _rows(rows)
    )


def _rows(rows: Sequence[CellsAndProofs]) -> list[tuple[list[bytes], list[bytes]]]:
    # The converter reads lists and tuples, so any other sequence becomes a list.
    return [(list(cells), list(proofs)) for cells, proofs in rows]


def process_operation(
    name: str,
    fork: str,
    handler: str,
    pre: bytes,
    operation: bytes,
    verify: bool = True,
    config: dict[str, Any] | None = None,
    execution_valid: bool = True,
) -> bytes:
    """The SSZ bytes of a beacon state after one block operation, or TransitionError."""
    return _native.consensus_process_operation(
        name, fork, handler, pre, operation, config, verify, execution_valid
    )


def process_epoch(
    name: str, fork: str, handler: str, pre: bytes, config: dict[str, Any] | None = None
) -> bytes:
    """The SSZ bytes of a beacon state after one epoch transition step, or TransitionError."""
    return _native.consensus_process_epoch(name, fork, handler, pre, config)


def rewards_deltas(
    name: str, fork: str, component: str, pre: bytes, config: dict[str, Any] | None = None
) -> bytes:
    """The SSZ bytes of the reward and penalty deltas of one kind of vote, or TransitionError."""
    return _native.consensus_rewards_deltas(name, fork, component, pre, config)


def rewards_deltas_batch(
    name: str, fork: str, components: list[str], pre: bytes, config: dict[str, Any] | None = None
) -> list[bytes]:
    """The SSZ bytes of the deltas of each named kind of vote, from one decode of the state."""
    return _native.consensus_rewards_deltas_batch(name, fork, components, pre, config)


def process_slots(
    name: str, fork: str, pre: bytes, slots: int, config: dict[str, Any] | None = None
) -> bytes:
    """The SSZ bytes of a beacon state some slots later, or TransitionError."""
    return _native.consensus_process_slots(name, fork, pre, config, slots)


def state_transition(
    name: str,
    fork: str,
    pre: bytes,
    block: bytes,
    verify: bool = True,
    config: dict[str, Any] | None = None,
) -> bytes:
    """The SSZ bytes of a beacon state after a signed block, or TransitionError."""
    return _native.consensus_state_transition(name, fork, pre, block, config, verify)


def state_transition_across(
    name: str,
    fork: str,
    pre: bytes,
    block_fork: str,
    block: bytes,
    verify: bool = True,
    config: dict[str, Any] | None = None,
) -> bytes:
    """The SSZ bytes of a state after a block of the same or a later fork, or TransitionError."""
    return _native.consensus_state_transition_across(
        name, fork, pre, block_fork, block, config, verify
    )


def state_transitions(
    name: str,
    fork: str,
    pre: bytes,
    blocks: Sequence[bytes],
    verify: bool = True,
    config: dict[str, Any] | None = None,
) -> bytes:
    """The SSZ bytes of a beacon state after signed blocks in order, or TransitionError."""
    return _native.consensus_state_transitions(name, fork, pre, list(blocks), config, verify)


def state_transitions_across(
    name: str,
    fork: str,
    pre: bytes,
    block_forks: list[str],
    blocks: Sequence[bytes],
    verify: bool = True,
    config: dict[str, Any] | None = None,
) -> bytes:
    """The SSZ bytes of a state after blocks of the same or later forks, or TransitionError."""
    return _native.consensus_state_transitions_across(
        name, fork, pre, block_forks, list(blocks), config, verify
    )


# A step of a fork choice case: its kind, then its data.
#
# A block may come alone, or with the blobs and proofs, or with the columns, that the node holds.
# A read is one bool, or the three parts it asks for.
# A payload verdict is the Engine API status and the latest valid hash, or None.
ForkChoiceStep: TypeAlias = (
    tuple[Literal["tick"], int]
    | tuple[
        Literal["block"],
        bytes | tuple[bytes, list[bytes], list[bytes]] | tuple[bytes, list[bytes]],
    ]
    | tuple[
        Literal[
            "attestation",
            "attester_slashing",
            "pow_block",
            "execution_payload",
            "payload_attestation_message",
        ],
        bytes,
    ]
    | tuple[Literal["checks"], bool | tuple[bool, bool, bytes | None]]
    | tuple[Literal["payload"], tuple[str, bytes | None]]
    | tuple[Literal["fast_confirmation"], None]
)


def fork_choice(
    name: str,
    fork: str,
    anchor_state: bytes,
    anchor_block: bytes,
    steps: list[ForkChoiceStep],
    verify: bool = True,
    # `Any`, because `dict` is invariant in its values.
    config: dict[str, Any] | None = None,
) -> list:
    """The outcome of each step of a fork choice case, from an anchor state and block."""
    # A step is (kind, data), and its data is one of these:
    # - the tick in seconds
    # - the SSZ bytes of a block, an attestation, an attester slashing or a PoW block
    # - for "checks", what the read asks
    #
    # A read given as one bool asks for the proposer head when it is True.
    # It may also be (proposer head, viable leaves, root or None).
    # Viable leaves asks for the leaves of the filtered tree with their weights.
    # A root asks for the votes of the payload committee on the block of the root.
    #
    # From Gloas an "execution_payload" step is a signed envelope in SSZ.
    # From Gloas a "payload_attestation_message" step is a vote of the payload committee in SSZ.
    # From Deneb a block may come as (block, blobs, proofs): the node holds those for it.
    # From Fulu a block may come as (block, columns): the node samples those SSZ columns for it.
    # An empty list of columns means that the node cannot get them.
    # A "payload" step is (status, latest valid hash or None).
    # It is the verdict of the execution layer on the payload of the next block before Gloas.
    # From Gloas it judges the payload of the next "execution_payload" step instead.
    # The status is given by its Engine API name.
    # A "fast_confirmation" step, with data None, runs the fast confirmation of the slot.
    return _native.consensus_fork_choice(
        name, fork, anchor_state, anchor_block, steps, verify, config
    )


# A query of the Beacon API: a state or a block identifier, or a state and a validator identifier.
# It is a tagged tuple, with the tag first.
ApiQuery: TypeAlias = tuple[Literal["state", "block"], str] | tuple[Literal["validator"], str, str]


def api_resolve(
    name: str,
    fork: str,
    anchor_state: bytes,
    anchor_block: bytes,
    steps: list[ForkChoiceStep],
    queries: list[ApiQuery],
    verify: bool = True,
) -> list:
    """Resolve Beacon API identifiers against the store after the steps of a fork choice case."""
    # The steps are those of `fork_choice`.
    # Each answer is a dict with the root and slot of the block, or of the block a state follows.
    # The dict also says whether that block is finalized, and gives the index of a validator.
    # An answer is ("found", the dict or None) or ("refused", code, message).
    # An identifier that names nothing in the store is found as None.
    # A text that is no identifier is refused with code 400.
    return _native.consensus_api_resolve(
        name, fork, anchor_state, anchor_block, steps, verify, queries
    )


def api_spec(name: str, config: dict[str, Any] | None = None) -> dict[str, Any]:
    """The Beacon API spec map of a preset and the configuration of the same name."""
    # A number is a str of decimal digits, bytes are a str of 0x and lowercase hex, a name is text.
    # A schedule is a list of dicts of decimal strs.
    # The values are `Any`, so that a caller indexes a schedule without narrowing it.
    return _native.consensus_api_spec(name, config)


def api_fork_schedule(name: str, config: dict[str, Any] | None = None) -> list[dict[str, str]]:
    """The Beacon API fork schedule of a configuration, Phase 0 first."""
    return _native.consensus_api_fork_schedule(name, config)


def api_deposit_contract(name: str, config: dict[str, Any] | None = None) -> dict[str, str]:
    """The Beacon API deposit contract of a configuration."""
    return _native.consensus_api_deposit_contract(name, config)


def api_genesis(
    name: str, fork: str, state: bytes, config: dict[str, Any] | None = None
) -> dict[str, str]:
    """The Beacon API genesis of a genesis state and a configuration, or ConsensusError."""
    # The time and the root come from the state, the version from the configuration.
    return _native.consensus_api_genesis(name, fork, state, config)


def api_state_query(
    name: str, fork: str, state: bytes, query: str, epoch: int | None = None
) -> dict[str, Any]:
    """The Beacon API response to a query that reads one field of a state, or ConsensusError."""
    # The query is the last segment of the endpoint path, such as "finality_checkpoints".
    # The response holds the data, and the version where the endpoint names one.
    # The flags execution_optimistic and finalized come from the store and are absent.
    # The values are `Any`, since the data differs by query.
    # Only "randao" takes an epoch; an epoch on another query, or an unknown query, has code 0.
    # A state before the fork that adds the field raises ConsensusError with code 400.
    return _native.consensus_api_state_query(name, fork, state, query, epoch)


def api_state_query_ssz(name: str, fork: str, state: bytes, query: str) -> bytes:
    """The Beacon API SSZ body of a query that reads one field of a state, or ConsensusError."""
    # Only the queues, the proposer lookahead and the builder fields have an SSZ body.
    return _native.consensus_api_state_query_ssz(name, fork, state, query)


def api_registry_query(
    name: str,
    fork: str,
    state: bytes,
    query: str,
    *,
    ids: list[str] | None = None,
    statuses: list[str] | None = None,
    in_query: bool = False,
) -> dict[str, Any]:
    """The Beacon API response to a query on the registries of a state, or ConsensusError."""
    # The query is the last segment of the endpoint path, such as "validator_balances".
    # The query "validator" is the endpoint for one validator, and needs exactly one id.
    # The ids and statuses are texts as the API writes them; None or an empty list means all ids.
    # Only "validators" and "builders" take statuses.
    # Only "validators" and "validator_balances" take in_query; more than 64 ids then raise 414.
    # An argument that the query does not take raises ConsensusError with code 0.
    # The flags execution_optimistic and finalized come from the store and are absent.
    return _native.consensus_api_registry_query(name, fork, state, query, ids, statuses, in_query)


def api_validator_balances_ssz(
    name: str, fork: str, state: bytes, *, ids: list[str] | None = None, in_query: bool = False
) -> bytes:
    """The Beacon API SSZ body of the validator balances answer, or ConsensusError."""
    # None or an empty list of ids means all validators.
    # Set in_query for ids that come in a query string, where more than 64 raise code 414.
    return _native.consensus_api_validator_balances_ssz(name, fork, state, ids, in_query)


def api_block_query(name: str, fork: str, block: bytes, query: str) -> dict[str, Any]:
    """The Beacon API response to a query on a signed block, or ConsensusError."""
    # The query is "block", "root", "attestations" or "blinded_block".
    # From Gloas, "blinded_block" raises code 400, since such a block has no blinded form.
    # The flags execution_optimistic and finalized come from the store and are absent.
    return _native.consensus_api_block_query(name, fork, block, query)


def api_blobs(
    name: str,
    fork: str,
    block: bytes,
    blobs: Sequence[bytes],
    *,
    hashes: Sequence[bytes] | None = None,
) -> dict[str, Any]:
    """The Beacon API blobs of a signed block, in commitment order, or ConsensusError."""
    # The blobs are those of the commitments of the block, one each, in order; else code 500.
    # With hashes, only the blobs whose commitment has one of these versioned hashes remain.
    # An empty list of hashes is a request for no blob, unlike None.
    # The flags execution_optimistic and finalized come from the store and are absent.
    chosen = None if hashes is None else list(hashes)
    return _native.consensus_api_blobs(name, fork, block, list(blobs), chosen)


def api_blobs_ssz(
    name: str,
    fork: str,
    block: bytes,
    blobs: Sequence[bytes],
    *,
    hashes: Sequence[bytes] | None = None,
) -> bytes:
    """The Beacon API SSZ body of the blobs of a signed block, or ConsensusError."""
    chosen = None if hashes is None else list(hashes)
    return _native.consensus_api_blobs_ssz(name, fork, block, list(blobs), chosen)


def api_block_query_ssz(name: str, fork: str, block: bytes, query: str) -> bytes:
    """The Beacon API SSZ body of a query on a signed block, or ConsensusError."""
    # The query is "block" or "blinded_block"; the others have no SSZ body.
    # From Gloas, "blinded_block" raises code 400, since such a block has no blinded form.
    return _native.consensus_api_block_query_ssz(name, fork, block, query)


def api_header(
    name: str,
    fork: str,
    anchor_state: bytes,
    anchor_block: bytes,
    steps: list[ForkChoiceStep],
    block: bytes,
    *,
    verify: bool = True,
) -> dict[str, Any]:
    """The Beacon API header of a signed block against a fork choice store, or ForkChoiceError."""
    # The steps are those of `fork_choice`; the block is the SSZ of a signed block.
    # The data holds the root, whether the block is on the chain of the head, and the header.
    # The flags execution_optimistic and finalized are not computed, so they are absent.
    # An API error carries its HTTP code in `.code`.
    return _native.consensus_api_header(
        name, fork, anchor_state, anchor_block, steps, verify, block
    )


def api_headers(
    name: str,
    fork: str,
    anchor_state: bytes,
    anchor_block: bytes,
    steps: list[ForkChoiceStep],
    headers: Sequence[bytes],
    *,
    slot: int | None = None,
    parent_root: bytes | None = None,
    verify: bool = True,
) -> dict[str, Any]:
    """The Beacon API headers that match the filters, or ForkChoiceError."""
    # The headers are the SSZ of the signed headers that the node holds, kept in their order.
    # With neither filter, the slot is that of the head; with only a parent root, any slot.
    # The store is built from the steps of a fork choice case.
    # An API error carries its HTTP code in `.code`; a store without a head gives 500.
    return _native.consensus_api_headers(
        name, fork, anchor_state, anchor_block, steps, verify, list(headers), slot, parent_root
    )


def api_columns(
    name: str,
    fork: str,
    sidecars: Sequence[bytes],
    *,
    indices: Sequence[int] | None = None,
) -> dict[str, Any]:
    """The Beacon API data column sidecars with the requested indices, or ConsensusError."""
    # The sidecars are the SSZ of those that the node holds for the block, kept in their order.
    # The source allows any order; this answer keeps the order of the input.
    # Before Fulu it raises code 400.
    chosen = None if indices is None else list(indices)
    return _native.consensus_api_columns(name, fork, list(sidecars), chosen)


def api_columns_ssz(
    name: str,
    fork: str,
    sidecars: Sequence[bytes],
    *,
    indices: Sequence[int] | None = None,
) -> bytes:
    """The Beacon API SSZ body of the requested data column sidecars, or ConsensusError."""
    chosen = None if indices is None else list(indices)
    return _native.consensus_api_columns_ssz(name, fork, list(sidecars), chosen)


def api_payload_envelope(
    name: str,
    fork: str,
    anchor_state: bytes,
    anchor_block: bytes,
    steps: list[ForkChoiceStep],
    root: bytes,
    envelope: bytes,
    *,
    verify: bool = True,
) -> dict[str, Any]:
    """The Beacon API signed payload envelope of a block, or ForkChoiceError."""
    # The store keeps envelopes without signatures, so the signed envelope is an input.
    # It is answered when its message has the root of the envelope stored for the block.
    # Otherwise, and before Gloas, it raises ForkChoiceError with code 404.
    return _native.consensus_api_payload_envelope(
        name, fork, anchor_state, anchor_block, steps, verify, root, envelope
    )


def api_payload_envelope_ssz(
    name: str,
    fork: str,
    anchor_state: bytes,
    anchor_block: bytes,
    steps: list[ForkChoiceStep],
    root: bytes,
    envelope: bytes,
    *,
    verify: bool = True,
) -> bytes:
    """The Beacon API SSZ body of the signed payload envelope of a block, or ForkChoiceError."""
    return _native.consensus_api_payload_envelope_ssz(
        name, fork, anchor_state, anchor_block, steps, verify, root, envelope
    )


# A light client update that a node knows: its period, the name of its fork and its SSZ bytes.
KnownUpdate: TypeAlias = tuple[int, str, bytes]


def api_light_client_bootstrap(
    name: str,
    fork: str,
    anchor_state: bytes,
    anchor_block: bytes,
    steps: list[ForkChoiceStep],
    root: bytes,
    config: dict[str, Any] | None = None,
    *,
    verify: bool = True,
) -> dict[str, Any]:
    """The Beacon API light client bootstrap of a block of the store, or ForkChoiceError."""
    # The configuration replaces values of the named one for the bootstrap, not the fork choice.
    # A block that the store lacks, or whose bootstrap cannot be built, raises code 404.
    return _native.consensus_api_light_client_bootstrap(
        name, fork, anchor_state, anchor_block, steps, verify, config, root
    )


def api_light_client_bootstrap_ssz(
    name: str,
    fork: str,
    anchor_state: bytes,
    anchor_block: bytes,
    steps: list[ForkChoiceStep],
    root: bytes,
    config: dict[str, Any] | None = None,
    *,
    verify: bool = True,
) -> bytes:
    """The Beacon API SSZ body of the light client bootstrap of a block, or ForkChoiceError."""
    return _native.consensus_api_light_client_bootstrap_ssz(
        name, fork, anchor_state, anchor_block, steps, verify, config, root
    )


def api_light_client_updates(
    name: str,
    known: Sequence[KnownUpdate],
    start_period: int,
    count: int,
    config: dict[str, Any] | None = None,
) -> list[dict[str, Any]]:
    """The Beacon API light client updates of a range of periods, as JSON, or ConsensusError."""
    return _native.consensus_api_light_client_updates(
        name, config, list(known), start_period, count
    )


def api_light_client_updates_ssz(
    name: str,
    genesis_validators_root: bytes,
    known: Sequence[KnownUpdate],
    start_period: int,
    count: int,
    config: dict[str, Any] | None = None,
) -> bytes:
    """The Beacon API SSZ body of the light client updates of a range, or ConsensusError."""
    return _native.consensus_api_light_client_updates_ssz(
        name, config, genesis_validators_root, list(known), start_period, count
    )


def api_light_client_decode_updates(
    name: str, genesis_validators_root: bytes, data: bytes, config: dict[str, Any] | None = None
) -> list[tuple[str, bytes]]:
    """The fork name and the SSZ bytes of each update of an SSZ updates body, or ConsensusError."""
    return _native.consensus_api_light_client_decode_updates(
        name, config, genesis_validators_root, data
    )


def api_light_client_latest(
    name: str, fork: str, kind: Literal["finality", "optimistic"], update: bytes | None
) -> dict[str, Any]:
    """The Beacon API latest finality or optimistic update, or ConsensusError with code 404."""
    return _native.consensus_api_light_client_latest(name, fork, kind, update)


def api_attestation_data(
    name: str,
    fork: str,
    anchor_state: bytes,
    anchor_block: bytes,
    steps: list[ForkChoiceStep],
    slot: int,
    committee_index: int,
    *,
    optimistic_roots: Sequence[bytes] = (),
    verify: bool = True,
) -> dict[str, Any]:
    """The Beacon API attestation data for a slot at the head of a store, or ForkChoiceError."""
    # The store is built from the steps of a fork choice case.
    # The committee index is read before Electra only; a request without one passes 0.
    # An API error carries its HTTP code in `.code`.
    # A head root among the optimistic roots raises code 503; a slot before the head, code 400.
    return _native.consensus_api_attestation_data(
        name,
        fork,
        anchor_state,
        anchor_block,
        steps,
        verify,
        list(optimistic_roots),
        slot,
        committee_index,
    )


def api_payload_attestation_data(
    name: str,
    fork: str,
    anchor_state: bytes,
    anchor_block: bytes,
    steps: list[ForkChoiceStep],
    slot: int,
    *,
    payload_present: bool,
    blob_data_available: bool,
    verify: bool = True,
) -> dict[str, Any] | None:
    """The Beacon API payload attestation data for a slot, None for 204, or ForkChoiceError."""
    # None means the chain of the head has no block at the slot.
    # An API error carries its HTTP code in `.code`.
    # Before Gloas the request raises code 400.
    return _native.consensus_api_payload_attestation_data(
        name,
        fork,
        anchor_state,
        anchor_block,
        steps,
        verify,
        slot,
        payload_present,
        blob_data_available,
    )


def api_fork_choice(
    name: str,
    fork: str,
    anchor_state: bytes,
    anchor_block: bytes,
    steps: list[ForkChoiceStep],
    *,
    optimistic_roots: Sequence[bytes] = (),
    config: dict[str, Any] | None = None,
    verify: bool = True,
) -> dict[str, Any]:
    """The Beacon API fork choice debug response of a store, or ForkChoiceError."""
    # The store is built from the steps of a fork choice case, with its own config if it has one.
    # The response has one node per block and payload status; before Gloas each node is "full".
    # A store whose tree cannot be read raises code 500.
    return _native.consensus_api_fork_choice(
        name, fork, anchor_state, anchor_block, steps, verify, list(optimistic_roots), config
    )


def api_chain_heads(
    name: str,
    fork: str,
    anchor_state: bytes,
    anchor_block: bytes,
    steps: list[ForkChoiceStep],
    *,
    optimistic_roots: Sequence[bytes] = (),
    config: dict[str, Any] | None = None,
    verify: bool = True,
) -> dict[str, Any]:
    """The Beacon API chain heads: the leaves of the fork choice tree, or ForkChoiceError."""
    # The store is built from the steps of a fork choice case, with its own config if it has one.
    # Each leaf appears once by its block root; a store that cannot be read raises code 500.
    return _native.consensus_api_chain_heads(
        name, fork, anchor_state, anchor_block, steps, verify, list(optimistic_roots), config
    )


def api_aggregate_attestation(
    name: str,
    fork: str,
    state: bytes,
    data_root: bytes,
    slot: int,
    committee_index: int,
    *,
    attestations: Sequence[bytes] = (),
    singles: Sequence[bytes] = (),
    optimistic_roots: Sequence[bytes] = (),
) -> dict[str, Any]:
    """The Beacon API aggregate of the collected attestations, or ConsensusError."""
    # Attestations count before Electra and single attestations from Electra, all as SSZ.
    # No match raises code 404; a block root of the data among the optimistic roots, code 503.
    # An API error carries its HTTP code in `.code`.
    return _native.consensus_api_aggregate_attestation(
        name,
        fork,
        state,
        list(attestations),
        list(singles),
        list(optimistic_roots),
        data_root,
        slot,
        committee_index,
    )


def api_sync_committee_contribution(
    name: str,
    fork: str,
    state: bytes,
    slot: int,
    subcommittee_index: int,
    root: bytes,
    *,
    messages: Sequence[bytes] = (),
    optimistic_roots: Sequence[bytes] = (),
) -> dict[str, Any]:
    """The Beacon API sync committee contribution of the collected messages, or ConsensusError."""
    # The messages are SSZ sync committee messages; the slot must be that of the state.
    # No match raises code 404; a root among the optimistic roots, code 503.
    # An API error carries its HTTP code in `.code`.
    return _native.consensus_api_sync_committee_contribution(
        name, fork, state, list(messages), list(optimistic_roots), slot, subcommittee_index, root
    )


def api_attestation_rewards(
    name: str,
    fork: str,
    state: bytes,
    epoch: int,
    *,
    ids: Sequence[str] = (),
    config: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """The Beacon API attestation rewards of an epoch, read from a state, or ConsensusError."""
    # The state answers for its previous epoch; another epoch, or the first one, raises code 404.
    # The identifiers are indices or public keys as the API writes them; none names every validator.
    # The flags execution_optimistic and finalized come from the store and are absent.
    return _native.consensus_api_attestation_rewards(name, fork, state, config, epoch, list(ids))


def api_sync_committee_rewards(
    name: str,
    fork: str,
    state: bytes,
    aggregate: bytes,
    *,
    ids: Sequence[str] = (),
) -> dict[str, Any]:
    """The Beacon API sync committee rewards of a block, or ConsensusError."""
    # The state is the one the sync aggregate step reads; a state before Altair raises code 400.
    # The identifiers are indices or public keys as the API writes them; none names every member.
    # The flags execution_optimistic and finalized come from the store and are absent.
    return _native.consensus_api_sync_committee_rewards(name, fork, state, aggregate, list(ids))


def api_block_rewards(
    name: str,
    fork: str,
    state: bytes,
    block: bytes,
    *,
    config: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """The Beacon API rewards of the proposer of a signed block, or ConsensusError."""
    # The state is the one at the slot of the block, before it; a failure raises code 500.
    # The flags execution_optimistic and finalized come from the store and are absent.
    return _native.consensus_api_block_rewards(name, fork, state, block, config)


def api_duties(
    name: str,
    fork: str,
    state: bytes,
    kind: str,
    epoch: int,
    genesis_root: bytes,
    *,
    indices: Sequence[int] = (),
    config: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """The Beacon API duties of an epoch, computed from a state, or ConsensusError."""
    # The kind is "attester", "proposer", "proposer_v2", "sync" or "ptc".
    # The proposer duties read no indices; the sync answer has no dependent root.
    # An epoch the state cannot answer for, or an index of no validator, raises code 400.
    # So does an empty list of indices for the attester, sync and PTC duties.
    # The first proposer version answers for the current epoch of the state only.
    # The flag execution_optimistic comes from the store and is absent.
    return _native.consensus_api_duties(
        name, fork, state, config, kind, epoch, list(indices), genesis_root
    )


def api_committees(
    name: str,
    fork: str,
    state: bytes,
    *,
    epoch: int | None = None,
    index: int | None = None,
    slot: int | None = None,
) -> dict[str, Any]:
    """The Beacon API beacon committees of an epoch of a state, or ConsensusError."""
    # The epoch defaults to that of the state; an epoch after the next one raises code 400.
    # A slot outside the epoch raises code 400; index and slot filter the committees.
    return _native.consensus_api_committees(name, fork, state, epoch, index, slot)


def api_sync_committees(
    name: str, fork: str, state: bytes, *, epoch: int | None = None
) -> dict[str, Any]:
    """The Beacon API sync committee of a state by validator indices, or ConsensusError."""
    # The epoch defaults to that of the state, and must be in its period or the next one.
    # A state before Altair, or an epoch in another period, raises code 400.
    return _native.consensus_api_sync_committees(name, fork, state, epoch)


def api_ptc(
    name: str,
    fork: str,
    state: bytes,
    config: dict[str, Any] | None = None,
    *,
    slot: int | None = None,
) -> dict[str, Any]:
    """The Beacon API payload timeliness committee of a slot of a state, or ConsensusError."""
    # The slot defaults to that of the state.
    # A state before Gloas, or a slot outside the window of the state, raises code 400.
    return _native.consensus_api_ptc(name, fork, state, config, slot)


def api_ptc_ssz(
    name: str,
    fork: str,
    state: bytes,
    config: dict[str, Any] | None = None,
    *,
    slot: int | None = None,
) -> bytes:
    """The Beacon API SSZ body of the payload timeliness committee of a slot, or ConsensusError."""
    return _native.consensus_api_ptc_ssz(name, fork, state, config, slot)


def api_validator_status(validator: dict[str, Any], balance: int, epoch: int) -> tuple[str, str]:
    """The Beacon API status of a validator and the name of its group, or ConsensusError."""
    # The validator is the JSON of the API, as api_json writes a Validator.
    # A Validator has the same fields at every fork, so the call takes no name and no fork.
    return _native.consensus_api_validator_status(validator, balance, epoch)


def api_builder_status(name: str, fork: str, state: bytes, index: int) -> str:
    """The Beacon API status of the builder at an index of a state, or ConsensusError."""
    return _native.consensus_api_builder_status(name, fork, state, index)


def gossip_validation(
    name: str,
    fork: str,
    anchor_state: bytes,
    anchor_block: bytes,
    topic: str,
    messages: Sequence[tuple[int, int, bytes] | tuple[int, int, bytes, str]],
    verify: bool = True,
    config: dict[str, Any] | None = None,
    blocks: Sequence[tuple[int, int | None, bytes] | tuple[int, int | None, bytes, bytes | None]]
    | None = None,
    finalized: tuple[int, bytes] | None = None,
) -> list[tuple[str, str | None]]:
    """The outcome of each gossip message of a topic, in turn, with the reason of a failure."""
    # A block after the anchor is (1 if failed, 2 if pending, else 0; payload status; SSZ bytes).
    # Kind 3 gives a block that the store holds already, such as the anchor, for its envelope.
    # From Gloas the SSZ bytes of the signed envelope of its payload may follow, or None for none.
    # A message is (arrival time in milliseconds, subnet ID, SSZ bytes).
    # A topic may follow, for a message of another topic than the case.
    return _native.consensus_gossip_validation(
        name,
        fork,
        anchor_state,
        anchor_block,
        list(blocks or []),
        finalized,
        topic,
        list(messages),
        config,
        verify,
    )


def initialize_genesis(
    name: str,
    fork: str,
    eth1_block_hash: bytes,
    eth1_timestamp: int,
    deposits: Sequence[bytes],
    verify: bool = True,
    config: dict[str, Any] | None = None,
) -> bytes:
    """The SSZ bytes of the candidate genesis state of a block and its deposits."""
    return _native.consensus_initialize_genesis(
        name, fork, eth1_block_hash, list(deposits), config, eth1_timestamp, verify
    )


def is_valid_genesis_state(
    name: str, fork: str, state: bytes, config: dict[str, Any] | None = None
) -> bool:
    """Whether a candidate genesis state launches the chain."""
    return _native.consensus_is_valid_genesis_state(name, fork, state, config)


def compute_weak_subjectivity_period(
    name: str, fork: str, state: bytes, config: dict[str, Any] | None = None
) -> int:
    """The weak subjectivity period of a state, in epochs, or WeakSubjectivityError."""
    return _native.consensus_compute_weak_subjectivity_period(name, fork, state, config)


def is_within_weak_subjectivity_period(
    name: str,
    fork: str,
    ws_state: bytes,
    ws_checkpoint: bytes,
    genesis_time_ms: int,
    time_ms: int,
    config: dict[str, Any] | None = None,
) -> bool:
    """Whether a checkpoint and its state are within the period at the two times of a store."""
    return _native.consensus_is_within_weak_subjectivity_period(
        name, fork, ws_state, ws_checkpoint, config, genesis_time_ms, time_ms
    )


# An item of a deposit tree in preorder: "node", which its two subtrees follow.
# Or a subtree: ("zero", height), ("leaf", root) or ("finalized", count, root).
DepositSubtree: TypeAlias = (
    Literal["node"]
    | tuple[Literal["zero"], int]
    | tuple[Literal["leaf"], bytes]
    | tuple[Literal["finalized"], int, bytes]
)
# A tree is its subtrees in preorder, its count of deposits, and its finalized block.
# Every function that reads a tree raises DepositTreeError when it has not that shape.
DepositTree: TypeAlias = tuple[list[DepositSubtree], int, tuple[bytes, int] | None]
# The finalized roots, the deposit root, the count, and the hash and height of the block.
DepositTreeSnapshot: TypeAlias = tuple[list[bytes], bytes, int, bytes, int]
# Deposit data of the chain: the deposit root, the deposit count and the block hash.
Eth1Data: TypeAlias = tuple[bytes, int, bytes]


def deposit_tree_new() -> DepositTree:
    """The deposit tree with no deposit."""
    return _native.consensus_deposit_tree_new()


def deposit_tree_push_leaf(tree: DepositTree, leaf: bytes) -> DepositTree:
    """The tree with one more deposit, by the root of its data, or DepositTreeError."""
    return _native.consensus_deposit_tree_push_leaf(tree, leaf)


def deposit_tree_push_leaves(tree: DepositTree, leaves: list[bytes]) -> DepositTree:
    """The tree after pushing deposits in order, by the roots of their data, or DepositTreeError."""
    return _native.consensus_deposit_tree_push_leaves(tree, leaves)


def deposit_tree_get_root(tree: DepositTree) -> bytes:
    """The deposit root of a tree, or DepositTreeError."""
    return _native.consensus_deposit_tree_get_root(tree)


def deposit_tree_finalize(
    tree: DepositTree, eth1_data: Eth1Data, execution_block_height: int
) -> DepositTree:
    """The tree finalized at deposit data and the height of its block, or DepositTreeError."""
    return _native.consensus_deposit_tree_finalize(tree, eth1_data, execution_block_height)


def deposit_tree_get_proof(tree: DepositTree, index: int) -> tuple[bytes, list[bytes]]:
    """The leaf at an index and its proof: 32 sibling roots, then the count, or DepositTreeError."""
    return _native.consensus_deposit_tree_get_proof(tree, index)


def deposit_tree_get_snapshot(tree: DepositTree) -> DepositTreeSnapshot:
    """The EIP-4881 snapshot of a finalized tree, or DepositTreeError."""
    return _native.consensus_deposit_tree_get_snapshot(tree)


def deposit_tree_from_snapshot(snapshot: DepositTreeSnapshot) -> DepositTree:
    """The tree rebuilt from an EIP-4881 snapshot, or DepositTreeError."""
    return _native.consensus_deposit_tree_from_snapshot(snapshot)


def deposit_tree_snapshot_calculate_root(snapshot: DepositTreeSnapshot) -> bytes:
    """The deposit root that a snapshot's finalized roots and count compute, or DepositTreeError."""
    return _native.consensus_deposit_tree_snapshot_calculate_root(snapshot)


def get_committee_assignment(
    name: str,
    fork: str,
    state: bytes,
    epoch: int,
    validator_index: int,
    config: dict[str, Any] | None = None,
) -> tuple[list[int], int, int] | None:
    """The committee, its index and its slot for a validator in an epoch, or None."""
    return _native.consensus_get_committee_assignment(
        name, fork, state, config, epoch, validator_index
    )


def is_proposer(
    name: str, fork: str, state: bytes, validator_index: int, config: dict[str, Any] | None = None
) -> bool:
    """Whether a validator proposes the block of the slot of a state."""
    return _native.consensus_is_proposer(name, fork, state, config, validator_index)


def is_assigned_to_sync_committee(
    name: str,
    fork: str,
    state: bytes,
    epoch: int,
    validator_index: int,
    config: dict[str, Any] | None = None,
) -> bool:
    """Whether a validator serves on the sync committee of the period of an epoch."""
    return _native.consensus_is_assigned_to_sync_committee(
        name, fork, state, config, epoch, validator_index
    )


def compute_subnets_for_sync_committee(
    name: str, fork: str, state: bytes, validator_index: int, config: dict[str, Any] | None = None
) -> list[int]:
    """The sync committee subnets of a validator for the next slot, in increasing order."""
    return _native.consensus_compute_subnets_for_sync_committee(
        name, fork, state, config, validator_index
    )


def get_ptc_assignment(
    name: str,
    fork: str,
    state: bytes,
    epoch: int,
    validator_index: int,
    config: dict[str, Any] | None = None,
) -> int | None:
    """The slot of an epoch whose payload timeliness committee holds a validator, or None."""
    return _native.consensus_get_ptc_assignment(name, fork, state, config, epoch, validator_index)


def get_upcoming_proposal_slots(
    name: str, fork: str, state: bytes, validator_index: int, config: dict[str, Any] | None = None
) -> list[int]:
    """The slots after the slot of a state that a validator proposes, in increasing order."""
    return _native.consensus_get_upcoming_proposal_slots(name, fork, state, config, validator_index)


def get_validator_signature(
    name: str,
    fork: str,
    state: bytes,
    duty: str,
    obj: bytes,
    secret_key: bytes,
    config: dict[str, Any] | None = None,
) -> bytes:
    """The 96-byte signature of the SSZ bytes of the object of a duty, by a secret key."""
    return _native.consensus_get_validator_signature(
        name, fork, state, config, duty, obj, secret_key
    )


def get_aggregate_signature(name: str, fork: str, attestations: list) -> bytes:
    """The 96-byte aggregate of the signatures of attestations given as SSZ bytes."""
    return _native.consensus_get_aggregate_signature(name, fork, attestations)


def get_attestation_data(
    name: str,
    fork: str,
    state: bytes,
    head_root: bytes,
    head_slot: int,
    committee_index: int,
    payload_status: int,
) -> bytes:
    """The attestation data of an attester from the head block and the state at its slot, as SSZ."""
    return _native.consensus_get_attestation_data(
        name, fork, state, head_root, head_slot, committee_index, payload_status
    )


def construct_attestation(
    name: str,
    fork: str,
    state: bytes,
    data: bytes,
    validator_index: int,
    secret_key: bytes,
    config: dict[str, Any] | None = None,
) -> bytes:
    """Before Electra, the attestation of a validator on attestation data, as SSZ bytes."""
    return _native.consensus_construct_attestation(
        name, fork, state, config, data, validator_index, secret_key
    )


def construct_single_attestation(
    name: str,
    fork: str,
    state: bytes,
    data: bytes,
    committee_index: int,
    validator_index: int,
    secret_key: bytes,
    config: dict[str, Any] | None = None,
) -> bytes:
    """From Electra, the single attestation of a validator in a committee, as SSZ bytes."""
    return _native.consensus_construct_single_attestation(
        name, fork, state, config, data, committee_index, validator_index, secret_key
    )


def construct_aggregate(
    name: str, fork: str, state: bytes, data: bytes, attestations: list
) -> bytes:
    """Before Electra, the aggregate of the attestations that vote for some data, as SSZ bytes."""
    return _native.consensus_construct_aggregate(name, fork, state, data, attestations)


def construct_aggregate_of_single_attestations(
    name: str, fork: str, state: bytes, data: bytes, committee_index: int, singles: list
) -> bytes:
    """From Electra, the aggregate of the single attestations of a committee, as SSZ bytes."""
    return _native.consensus_construct_aggregate_of_single_attestations(
        name, fork, state, data, committee_index, singles
    )


def construct_sync_committee_contribution(
    name: str,
    fork: str,
    state: bytes,
    committee: bytes,
    block_root: bytes,
    subcommittee_index: int,
    messages: list,
) -> bytes:
    """From Altair, the contribution of a subcommittee from its messages, as SSZ bytes."""
    return _native.consensus_construct_sync_committee_contribution(
        name, fork, state, committee, block_root, subcommittee_index, messages
    )


def read_slashing_interchange(text: bytes) -> bytes:
    """An EIP-3076 interchange file read and written again, as JSON text."""
    return _native.consensus_read_slashing_interchange(text)


def import_slashing_interchange(held: bytes, file: bytes) -> bytes:
    """The record after importing a file with the minimal strategy of EIP-3076."""
    return _native.consensus_import_slashing_interchange(held, file)


def check_block_signing(interchange: bytes, pubkey: bytes, slot: int, signing_root: bytes) -> None:
    """Return if a key may sign a block, or raise the SlashingProtectionError of its condition."""
    _native.consensus_check_block_signing(interchange, pubkey, slot, signing_root)


def check_attestation_signing(
    interchange: bytes, pubkey: bytes, source_epoch: int, target_epoch: int, signing_root: bytes
) -> None:
    """Return if a key may sign a vote, or raise the SlashingProtectionError of its condition."""
    _native.consensus_check_attestation_signing(
        interchange, pubkey, source_epoch, target_epoch, signing_root
    )


def record_block_signing(
    interchange: bytes, pubkey: bytes, slot: int, signing_root: bytes
) -> bytes:
    """The record after a key signs a block, as JSON text."""
    return _native.consensus_record_block_signing(interchange, pubkey, slot, signing_root)


def record_attestation_signing(
    interchange: bytes, pubkey: bytes, source_epoch: int, target_epoch: int, signing_root: bytes
) -> bytes:
    """The record after a key signs a vote, as JSON text."""
    return _native.consensus_record_attestation_signing(
        interchange, pubkey, source_epoch, target_epoch, signing_root
    )


def is_execution_block(name: str, fork: str, block: bytes) -> bool:
    """From Bellatrix, whether a block has a non-empty payload; from Gloas, a nonzero bid hash."""
    return _native.consensus_is_execution_block(name, fork, block)


def is_optimistic_candidate_block(
    name: str, fork: str, blocks: list, current_slot: int, block: bytes, safe_slots: int = 128
) -> bool:
    """From Bellatrix, whether a block may be imported optimistically, given the known blocks."""
    return _native.consensus_is_optimistic_candidate_block(
        name, fork, blocks, current_slot, safe_slots, block
    )


def latest_verified_ancestor(
    name: str,
    fork: str,
    blocks: Sequence[bytes],
    optimistic_roots: Sequence[bytes],
    root: bytes,
    payload_status: int = 2,
) -> bytes:
    """From Bellatrix, the root of the latest block of a chain that is not optimistic."""
    # The status of the payload of the block in the node: 0 empty, 1 full and 2 pending.
    # From Gloas the status matters: a pending node holds only the payloads its block builds on.
    return _native.consensus_latest_verified_ancestor(
        name, fork, list(blocks), list(optimistic_roots), root, payload_status
    )


def on_valid_payload(
    name: str, fork: str, blocks: Sequence[bytes], optimistic_roots: Sequence[bytes], root: bytes
) -> list[bytes]:
    """From Bellatrix, the optimistic roots after the payload of a block is found valid."""
    return _native.consensus_on_valid_payload(
        name, fork, list(blocks), list(optimistic_roots), root
    )


def on_invalidated_payload(
    name: str, fork: str, blocks: Sequence[bytes], optimistic_roots: Sequence[bytes], first: bytes
) -> list[bytes]:
    """From Bellatrix, the optimistic roots after a block is found to be the first invalid one."""
    return _native.consensus_on_invalidated_payload(
        name, fork, list(blocks), list(optimistic_roots), first
    )


def is_optimistic_node(
    name: str,
    fork: str,
    anchor_state: bytes,
    anchor_block: bytes,
    steps: Sequence[ForkChoiceStep],
    optimistic_roots: Sequence[bytes],
    head: bytes,
    verify: bool = True,
    # `Any`, because `dict` is invariant in its values.
    config: dict[str, Any] | None = None,
    head_payload_status: int = 2,
) -> bool:
    """From Bellatrix, whether a node is optimistic after the steps of a fork choice run."""
    # The status of the payload of the head: 0 empty, 1 full and 2 pending, read from Gloas.
    # A pending head is optimistic when its own payload or the one it builds on is.
    return _native.consensus_is_optimistic_node(
        name,
        fork,
        anchor_state,
        anchor_block,
        list(steps),
        verify,
        config,
        list(optimistic_roots),
        head,
        head_payload_status,
    )


def inclusion_list_satisfaction(
    name: str,
    fork: str,
    anchor_state: bytes,
    anchor_block: bytes,
    steps: Sequence[ForkChoiceStep],
    validation_status: int,
    satisfied: bool,
    roots: Sequence[bytes],
    *,
    validated_root: bytes | None = None,
    verify: bool = True,
    # `Any`, because `dict` is invariant in its values.
    config: dict[str, Any] | None = None,
) -> list[bool | None]:
    """From Heze, the recorded inclusion list answers for the roots after a fork choice run."""
    # Every payload has one validation status, 0 valid, 1 invalidated or 2 not validated.
    # The execution layer gives every payload the same answer, `satisfied`.
    # Only a payload kept not validated is optimistic, so only it can turn valid.
    # `validated_root`, if given, names such a payload, which then turns valid with `satisfied`.
    return _native.consensus_inclusion_list_satisfaction(
        name,
        fork,
        anchor_state,
        anchor_block,
        list(steps),
        verify,
        config,
        validation_status,
        satisfied,
        validated_root,
        list(roots),
    )


def is_optimistic_restricted_domain(domain_type: bytes) -> bool:
    """Whether an optimistic validator may not sign under a domain type of 4 bytes."""
    return _native.consensus_is_optimistic_restricted_domain(domain_type)


def get_eth1_vote(
    name: str,
    fork: str,
    state: bytes,
    chain: Sequence[tuple[int, bytes]],
    config: dict[str, Any] | None = None,
) -> bytes:
    """The Eth1 data that a proposer votes for, from Eth1 blocks as (timestamp, Eth1 data)."""
    return _native.consensus_get_eth1_vote(name, fork, state, config, list(chain))


def get_eth1_pending_deposit_count(name: str, fork: str, state: bytes) -> int:
    """In Electra, the number of deposits of the deposit contract that a block holds."""
    return _native.consensus_get_eth1_pending_deposit_count(name, fork, state)


def compute_new_state_root(
    name: str,
    fork: str,
    state: bytes,
    block: bytes,
    verify: bool = True,
    config: dict[str, Any] | None = None,
) -> bytes:
    """The 32-byte root of the state after a block, to set as the state root of that block."""
    return _native.consensus_compute_new_state_root(name, fork, state, block, config, verify)


def compute_on_chain_aggregate(name: str, fork: str, aggregates: list) -> bytes:
    """The attestation on chain from network aggregates of the same data, as SSZ bytes."""
    return _native.consensus_compute_on_chain_aggregate(name, fork, aggregates)


def process_sync_committee_contributions(name: str, fork: str, contributions: list) -> bytes:
    """From Altair, the sync aggregate of a block from contributions, as SSZ bytes."""
    return _native.consensus_process_sync_committee_contributions(name, fork, contributions)


def get_execution_requests(name: str, fork: str, requests: list) -> bytes:
    """The requests of an execution block from the typed lists of the execution layer."""
    return _native.consensus_get_execution_requests(name, fork, requests)


def get_execution_payload_bid(
    name: str,
    fork: str,
    state: bytes,
    payload: bytes,
    requests: bytes,
    commitments: bytes,
    slot: int,
    fee_recipient: bytes,
    builder_index: int,
    value: int,
    inclusion_list_bits: bytes | None = None,
) -> bytes:
    """
    From Gloas, the bid of a builder for a payload it built on a state, as SSZ bytes.

    The inclusion list bits are SSZ bytes, required from Heze and rejected before.
    """
    # Empty bytes tell the export that the bits are absent.
    return _native.consensus_get_execution_payload_bid(
        name,
        fork,
        state,
        payload,
        requests,
        commitments,
        fee_recipient,
        inclusion_list_bits or b"",
        slot,
        builder_index,
        value,
    )


def get_self_built_execution_payload_bid(
    name: str,
    fork: str,
    state: bytes,
    payload: bytes,
    requests: bytes,
    commitments: bytes,
    fee_recipient: bytes,
    inclusion_list_bits: bytes | None = None,
) -> bytes:
    """
    From Gloas, the signed bid of a proposer that builds its own payload, as SSZ bytes.

    The inclusion list bits are SSZ bytes, required from Heze and rejected before.
    """
    # Empty bytes tell the export that the bits are absent.
    return _native.consensus_get_self_built_execution_payload_bid(
        name,
        fork,
        state,
        payload,
        requests,
        commitments,
        fee_recipient,
        inclusion_list_bits or b"",
    )


def get_execution_payload_envelope(
    name: str, fork: str, block: bytes, payload: bytes, requests: bytes
) -> bytes:
    """From Gloas, the envelope that reveals a payload after the block of its bid, as SSZ bytes."""
    return _native.consensus_get_execution_payload_envelope(name, fork, block, payload, requests)


def get_validators_custody_requirement(
    name: str,
    fork: str,
    state: bytes,
    validator_indices: Sequence[int],
    config: dict[str, Any] | None = None,
) -> int:
    """The number of custody groups of a node with these validators."""
    return _native.consensus_get_validators_custody_requirement(
        name, fork, state, config, list(validator_indices)
    )


def upgrade_state(
    name: str, fork: str, pre: bytes, verify: bool = True, config: dict[str, Any] | None = None
) -> bytes:
    """The SSZ bytes of a state upgraded to a fork from the fork before, or TransitionError."""
    return _native.consensus_upgrade_state(name, fork, pre, config, verify)


__all__ = [
    "preset",
    "config",
    "parameters",
    "ConsensusError",
    "get_custody_groups",
    "get_custody_column_bits",
    "compute_columns_for_custody_group",
    "ssz_static",
    "api_json",
    "api_ssz",
    "builder_api_json",
    "builder_api_ssz",
    "api_spec",
    "api_fork_schedule",
    "api_deposit_contract",
    "api_genesis",
    "api_state_query",
    "api_state_query_ssz",
    "api_registry_query",
    "api_validator_balances_ssz",
    "api_block_query",
    "api_blobs",
    "api_blobs_ssz",
    "api_block_query_ssz",
    "api_header",
    "api_headers",
    "api_columns",
    "api_columns_ssz",
    "api_payload_envelope",
    "api_payload_envelope_ssz",
    "api_light_client_bootstrap",
    "api_light_client_bootstrap_ssz",
    "api_light_client_decode_updates",
    "api_light_client_latest",
    "api_light_client_updates",
    "api_light_client_updates_ssz",
    "KnownUpdate",
    "api_attestation_data",
    "api_payload_attestation_data",
    "api_fork_choice",
    "api_chain_heads",
    "api_aggregate_attestation",
    "api_sync_committee_contribution",
    "api_attestation_rewards",
    "api_sync_committee_rewards",
    "api_block_rewards",
    "api_duties",
    "api_committees",
    "api_sync_committees",
    "api_ptc",
    "api_ptc_ssz",
    "api_validator_status",
    "api_builder_status",
    "is_valid_builder_signature",
    "process_registration",
    "is_eligible_for_bid",
    "process_bid",
    "is_eligible_for_bid_gloas",
    "validate_bid",
    "unblind_signed_blinded_block",
    "verify_builder_request_auth_signature",
    "builder_request_auth_failures",
    "builder_preferences_failures",
    "default_auth_data",
    "relay_submission_bid",
    "relay_validators",
    "relay_delivered_payload",
    "relay_received_bid",
    "relay_delivered_keeps",
    "relay_received_keeps",
    "relay_sort_delivered",
    "builder_bid_value",
    "consensus_version",
    "consensus_version_fork",
    "upgrade_operation",
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
    "gossip_topic_bound",
    "reqresp_request_bounds",
    "reqresp_response_bounds",
    "ResponseBlock",
    "ResponseSidecar",
    "ResponseEnvelope",
    "ResponseInclusionList",
    "ResponseItems",
    "reqresp_is_valid_response",
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
    "CellsAndProofs",
    "recover_matrix",
    "get_data_column_sidecars_from_block",
    "get_data_column_sidecars_from_column_sidecar",
    "TransitionError",
    "WeakSubjectivityError",
    "ValidatorDutyError",
    "ProposerError",
    "SlashingProtectionError",
    "read_slashing_interchange",
    "import_slashing_interchange",
    "check_block_signing",
    "check_attestation_signing",
    "record_block_signing",
    "record_attestation_signing",
    "process_operation",
    "LightClientError",
    "ForkChoiceError",
    "fork_choice",
    "gossip_validation",
    "light_client_sync",
    "SyncStep",
    "SyncHeader",
    "block_to_light_client_header",
    "light_client_update_proofs",
    "is_better_update",
    "genesis_block",
    "create_light_client_bootstrap",
    "create_light_client_update",
    "light_client_update_as",
    "GossipOutcome",
    "UpdateType",
    "light_client_gossip_full_node",
    "light_client_gossip_light_client",
    "compute_fork_digest",
    "digest_epochs",
    "fork_of_digest",
    "digests_identify",
    "process_epoch",
    "rewards_deltas",
    "rewards_deltas_batch",
    "upgrade_state",
    "compute_weak_subjectivity_period",
    "is_within_weak_subjectivity_period",
    "DepositTreeError",
    "DepositSubtree",
    "DepositTree",
    "DepositTreeSnapshot",
    "Eth1Data",
    "deposit_tree_push_leaves",
    "deposit_tree_new",
    "deposit_tree_push_leaf",
    "deposit_tree_get_root",
    "deposit_tree_finalize",
    "deposit_tree_get_proof",
    "deposit_tree_get_snapshot",
    "deposit_tree_from_snapshot",
    "deposit_tree_snapshot_calculate_root",
    "get_committee_assignment",
    "is_proposer",
    "is_assigned_to_sync_committee",
    "compute_subnets_for_sync_committee",
    "get_ptc_assignment",
    "get_upcoming_proposal_slots",
    "get_validator_signature",
    "is_execution_block",
    "is_optimistic_candidate_block",
    "is_optimistic_node",
    "inclusion_list_satisfaction",
    "latest_verified_ancestor",
    "on_valid_payload",
    "on_invalidated_payload",
    "is_optimistic_restricted_domain",
    "get_aggregate_signature",
    "get_attestation_data",
    "construct_attestation",
    "construct_single_attestation",
    "construct_aggregate",
    "construct_aggregate_of_single_attestations",
    "construct_sync_committee_contribution",
    "get_eth1_vote",
    "get_eth1_pending_deposit_count",
    "compute_new_state_root",
    "compute_on_chain_aggregate",
    "process_sync_committee_contributions",
    "get_execution_requests",
    "get_execution_payload_bid",
    "get_self_built_execution_payload_bid",
    "get_execution_payload_envelope",
    "get_validators_custody_requirement",
    "process_slots",
    "state_transition",
    "state_transition_across",
    "state_transitions",
    "state_transitions_across",
]
