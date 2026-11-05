"""The consensus layer: presets, configurations, containers, the shuffle, custody and networking."""

import json
from typing import Any

from ..errors import ConsensusError, LightClientError, TransitionError

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ..cryptography import _native


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
        raise ValueError("node_id or custody_group_count is out of range")
    groups = _native.consensus_get_custody_groups(
        name, node_id.to_bytes(32, "big"), custody_group_count
    )
    return _value(json.loads(groups))


def compute_columns_for_custody_group(custody_group: int, name: str = "mainnet") -> list:
    """The columns of a custody group, or ConsensusError for a group out of range."""
    if not 0 <= custody_group < 2**64:
        raise ValueError("custody_group is out of range")
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


def pq_keys_possession_signing_root(genesis_validators_root: bytes, pubkey: bytes,
                                    xmss_public_key: bytes, name: str = "mainnet") -> bytes:
    """The root that an EIP-8450 proof of possession signs."""
    return _native.pq_keys_possession_signing_root(name, genesis_validators_root, pubkey,
                                                   xmss_public_key)


def pq_keys_is_valid_possession_proof(genesis_validators_root: bytes, pubkey: bytes,
                                      xmss_public_key: bytes, proof: bytes,
                                      name: str = "mainnet") -> bool:
    """Whether an EIP-8450 proof of possession is valid."""
    return _native.pq_keys_is_valid_possession_proof(name, genesis_validators_root, pubkey,
                                                     xmss_public_key, proof)


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
        raise ValueError("node_id is out of range")
    subnets = _native.consensus_compute_subscribed_subnets(name, node_id.to_bytes(32, "big"), epoch)
    return _value(json.loads(subnets))


def merkle_proof(name: str, fork: str, type_name: str, data: bytes, gindex: int) -> tuple:
    """The node at a generalized index of a beacon container, and its branch up to the root."""
    out = _native.consensus_merkle_proof(name, fork, type_name, data, gindex)
    return out[:32], [out[i:i + 32] for i in range(32, len(out), 32)]


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
    offsets = [int.from_bytes(data[i:i + 4], "little") for i in range(0, first, 4)]
    return [data[a:b] for a, b in zip(offsets, offsets[1:] + [len(data)])]


def verify_data_column_sidecar(name: str, fork: str, data: bytes,
                               config: dict | None = None) -> bool:
    """Whether a data column sidecar has a valid shape under the blob limit of its epoch."""
    replacements = json.dumps(config).encode() if config else b""
    return _native.consensus_verify_data_column_sidecar(name, fork, data, replacements)


def verify_data_column_sidecar_inclusion_proof(name: str, fork: str, data: bytes) -> bool:
    """Whether the branch of a data column sidecar climbs from its commitments to its body root."""
    return _native.consensus_verify_data_column_sidecar_inclusion_proof(name, fork, data)


def verify_data_column_sidecar_kzg_proofs(name: str, fork: str, data: bytes) -> bool:
    """Whether the cells of a data column sidecar match its commitments by their proofs."""
    return _native.consensus_verify_data_column_sidecar_kzg_proofs(name, fork, data)


def light_client_sync(name: str, fork: str, trusted_block_root: bytes,
                      genesis_validators_root: bytes, bootstrap: bytes, steps: list,
                      config: dict | None = None) -> list:
    """The finalized and optimistic headers, as slot and two roots, after each step of a sync."""
    # A step is a slot and an update, or a slot and None to force an update at that slot.
    replacements = json.dumps(config).encode() if config else b""
    records = b"".join(slot.to_bytes(8, "little") + len(update or b"").to_bytes(4, "little")
                       + (update or b"") for slot, update in steps)
    out = _native.consensus_light_client_sync(name, fork, replacements, trusted_block_root,
                                              genesis_validators_root, bootstrap, records)

    def header(record: bytes) -> tuple:
        return int.from_bytes(record[:8], "little"), record[8:40], record[40:72]

    return [(header(out[i:i + 72]), header(out[i + 72:i + 144]))
            for i in range(0, len(out), 144)]


def is_better_update(name: str, fork: str, new_update: bytes, old_update: bytes) -> bool:
    """Whether a new light client update ranks above an old one for a forced update."""
    return _native.consensus_is_better_update(name, fork, new_update, old_update)


def compute_fork_digest(name: str, genesis_validators_root: bytes, epoch: int,
                        config: dict | None = None) -> bytes:
    """The fork digest at an epoch, on the chain with the given root of the genesis validators."""
    replacements = json.dumps(config).encode() if config else b""
    return _native.consensus_compute_fork_digest(name, replacements, genesis_validators_root,
                                                 epoch)


def compute_matrix(blobs: list) -> list:
    """The entries of the matrix of the blobs, each in its SSZ encoding."""
    out = _native.consensus_compute_matrix(b"".join(blobs))
    return [out[i:i + MATRIX_ENTRY_BYTES] for i in range(0, len(out), MATRIX_ENTRY_BYTES)]


def recover_matrix(entries: list, blob_count: int) -> list:
    """The entries of the full matrix of `blob_count` rows, recovered from some of its entries."""
    out = _native.consensus_recover_matrix(b"".join(entries), blob_count)
    return [out[i:i + MATRIX_ENTRY_BYTES] for i in range(0, len(out), MATRIX_ENTRY_BYTES)]


def get_data_column_sidecars_from_block(name: str, fork: str, block: bytes, rows: list) -> list:
    """The data column sidecars of a signed block, from the cells and proofs of each blob."""
    joined = b"".join(b"".join(cells) + b"".join(proofs) for cells, proofs in rows)
    return _list_items(
        _native.consensus_get_data_column_sidecars_from_block(name, fork, block, joined))


def get_data_column_sidecars_from_column_sidecar(name: str, fork: str, sidecar: bytes,
                                                 rows: list) -> list:
    """All the data column sidecars of a block, from one of them and the cells of each blob."""
    joined = b"".join(b"".join(cells) + b"".join(proofs) for cells, proofs in rows)
    return _list_items(_native.consensus_get_data_column_sidecars_from_column_sidecar(
        name, fork, sidecar, joined))


def process_operation(name: str, fork: str, handler: str, pre: bytes, operation: bytes,
                      verify: bool = True) -> bytes:
    """The SSZ bytes of a beacon state after one block operation, or TransitionError."""
    return _native.consensus_process_operation(name, fork, handler, pre, operation, verify)


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
    "compute_matrix",
    "recover_matrix",
    "get_data_column_sidecars_from_block",
    "get_data_column_sidecars_from_column_sidecar",
    "TransitionError",
    "process_operation",
    "LightClientError",
    "light_client_sync",
    "is_better_update",
    "compute_fork_digest",
]
