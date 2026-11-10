"""The Engine API between the consensus and the execution layers."""

from collections.abc import Sequence
from typing import Any, TypeAlias

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.consensus import ForkChoiceStep
from ethlib.cryptography import _native
from ethlib.errors import EngineError, JwtError, ProposerError
from ethlib.execution.blocks import RecentBlock


def jwt_build(secret: bytes, issued_at: int) -> str:
    """Build an HS256 Engine token from a 32-byte secret and an issued-at time in seconds."""
    return _native.engine_jwt_build(secret, issued_at)


def jwt_check(secret: bytes, token: str, clock: int) -> bool:
    """Accept an HS256 Engine token only within 60 seconds of its issued-at time."""
    return _native.engine_jwt_check(secret, token, clock)


def new_payload(config: dict, method: str, params: list) -> dict:
    """The payload status of an `engine_newPayload` call, without the state of the parent."""
    request = {"jsonrpc": "2.0", "id": 1, "method": method, "params": params}
    return _native.engine_new_payload(config, request)


def new_payload_on_chain(
    config: dict, state: bytes, recent: Sequence[RecentBlock], method: str, params: list
) -> tuple[dict, bytes | None, bytes | None]:
    """The payload status of an `engine_newPayload` call, on a chain that holds the parent."""
    # A valid payload also gives the RLP encodings of its header and of the accounts after it.
    request = {"jsonrpc": "2.0", "id": 1, "method": method, "params": params}
    items = [(name, header, list(ommers)) for name, header, ommers in recent]
    return _native.engine_new_payload_on_chain(config, state, items, request)


def build_payload(
    config: dict,
    state: bytes,
    recent: Sequence[RecentBlock],
    method: str,
    attributes: dict,
    *,
    fee_recipient: bytes,
    extra_data: bytes,
    target_gas_limit: int,
    transactions: Sequence[bytes],
) -> tuple[bytes, bytes, list[bytes], int]:
    """The block that payload attributes build on a chain, its accounts, requests and value."""
    # The attributes pass the checks of the forkchoice update `method` against the last block.
    items = [(name, header, list(ommers)) for name, header, ommers in recent]
    return _native.engine_build_payload(
        config,
        state,
        items,
        method,
        attributes,
        fee_recipient,
        extra_data,
        target_gas_limit,
        list(transactions),
    )


def forkchoice_updated(
    config: dict, tree: list, method: str, params: list, finalized: str | None = None
) -> dict:
    """The response to an `engine_forkchoiceUpdated` call, against a tree of known payloads."""
    # Each payload of the tree has a block hash, a parent hash, a validity, a number and a time.
    # The execution layer may know a finalized block, the latest one an earlier update named.
    request = {"jsonrpc": "2.0", "id": 1, "method": method, "params": params}
    return _native.engine_forkchoice_updated(config, tree, finalized, request)


# One entry of a blob pool: the versioned hash, the blob, the blob proof, and the 128 cells.
# Each item of the cells is a cell and its proof, or None where the pool lacks it.
# None in place of the cells means that the pool holds no cell of the blob.
# A pool holds each versioned hash once, and takes requests of at least 128 hashes.
PoolEntry: TypeAlias = tuple[
    bytes, bytes | None, bytes | None, Sequence[tuple[bytes, bytes] | None] | None
]


def get_blobs(
    pool: Sequence[PoolEntry],
    fork: str,
    method: str,
    params: list,
    *,
    serving: bool = True,
    max_request: int = 128,
) -> list[dict[str, Any] | None] | None:
    """The answer to an `engine_getBlobs` call, from a blob pool at the active fork of the node."""
    request = {"jsonrpc": "2.0", "id": 1, "method": method, "params": params}
    entries = [
        (versioned_hash, blob, proof, None if cells is None else list(cells))
        for versioned_hash, blob, proof, cells in pool
    ]
    return _native.engine_get_blobs(entries, serving, max_request, fork, request)


# One withdrawal of a body: the index, the validator index, the 20-byte address and the amount.
WithdrawalEntry: TypeAlias = tuple[int, int, bytes, int]

# One block of a store of bodies: the block hash, its number if canonical, and its fork.
# Then come its transactions, its withdrawals (None before Shapella) and its block access list.
# The access list is None before Glamsterdam, and from Glamsterdam when the node pruned it.
# A store holds each hash once, one canonical block per number, and one at the latest number.
BodyEntry: TypeAlias = tuple[
    bytes, int | None, str, Sequence[bytes], Sequence[WithdrawalEntry] | None, bytes | None
]


def get_payload_bodies(
    store: Sequence[BodyEntry], latest: int, method: str, params: list, *, max_request: int = 32
) -> list[dict[str, Any] | None]:
    """The answer to an `engine_getPayloadBodiesByHash` or `ByRange` call, from a store."""
    request = {"jsonrpc": "2.0", "id": 1, "method": method, "params": params}
    entries = [
        (
            block_hash,
            number,
            fork,
            list(transactions),
            None if withdrawals is None else list(withdrawals),
            access_list,
        )
        for block_hash, number, fork, transactions, withdrawals, access_list in store
    ]
    return _native.engine_get_payload_bodies(entries, latest, max_request, request)


# An ID, fork, payload JSON value, block value, network blob transactions, requests and override.
PayloadEntry: TypeAlias = tuple[
    bytes, str, dict, int, Sequence[bytes], Sequence[bytes] | None, bool
]


def get_payload(config: dict, store: Sequence[PayloadEntry], method: str, params: list) -> dict:
    """The latest completed payload of a build, with its checked blobs bundle."""
    request = {"jsonrpc": "2.0", "id": 1, "method": method, "params": params}
    entries = [
        (
            identifier,
            fork,
            payload,
            value,
            list(network),
            None if requests is None else list(requests),
            override,
        )
        for identifier, fork, payload, value, network, requests, override in store
    ]
    return _native.engine_get_payload(config, entries, request)


def prepare_execution_payload(
    name: str,
    fork: str,
    state: bytes,
    safe_block_hash: bytes,
    finalized_block_hash: bytes,
    suggested_fee_recipient: bytes,
    pow_chain: list | None = None,
    config: dict | None = None,
) -> dict | None:
    """The forkchoice update and payload attributes of a proposer, or None when it asks nothing."""
    return _native.engine_prepare_execution_payload(
        name,
        fork,
        state,
        config,
        safe_block_hash,
        finalized_block_hash,
        suggested_fee_recipient,
        pow_chain or [],
    )


def prepare_execution_payload_gloas(
    name: str,
    fork: str,
    anchor_state: bytes,
    anchor_block: bytes,
    steps: list[ForkChoiceStep],
    head_root: bytes,
    head_status: int,
    state: bytes,
    safe_block_hash: bytes,
    suggested_fee_recipient: bytes,
    target_gas_limit: int,
    custody_columns: bytes | None = None,
    verify: bool = True,
    # `Any`, because `dict` is invariant in its values.
    config: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """From Gloas: the forkchoice update and payload attributes of a proposer on a store."""
    # The steps take the form of those of `consensus.fork_choice`, which build the store.
    # The head status is 0 for empty, 1 for full and 2 for pending.
    # The finalized block hash is that of the store.
    # The custody columns are the 16 bytes of `consensus.get_custody_column_bits`, or None.
    return _native.engine_prepare_execution_payload_gloas(
        name,
        fork,
        anchor_state,
        anchor_block,
        steps,
        head_root,
        head_status,
        state,
        safe_block_hash,
        suggested_fee_recipient,
        target_gas_limit,
        custody_columns,
        verify,
        config,
    )


def finalized_execution_block_hash(
    name: str,
    fork: str,
    anchor_state: bytes,
    anchor_block: bytes,
    steps: list[ForkChoiceStep],
    verify: bool = True,
    # `Any`, because `dict` is invariant in its values.
    config: dict[str, Any] | None = None,
) -> bytes:
    """From Bellatrix: the finalized block hash of an update on a store, or ForkChoiceError."""
    # The steps take the form of those of `consensus.fork_choice`, which build the store.
    return _native.engine_finalized_execution_block_hash(
        name, fork, anchor_state, anchor_block, steps, verify, config
    )


__all__ = [
    "jwt_build",
    "jwt_check",
    "new_payload",
    "new_payload_on_chain",
    "forkchoice_updated",
    "get_blobs",
    "PoolEntry",
    "get_payload_bodies",
    "get_payload",
    "PayloadEntry",
    "BodyEntry",
    "WithdrawalEntry",
    "prepare_execution_payload",
    "prepare_execution_payload_gloas",
    "finalized_execution_block_hash",
    "EngineError",
    "JwtError",
    "ProposerError",
]
