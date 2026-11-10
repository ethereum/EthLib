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


def forkchoice_updated(tree: list, method: str, params: list, finalized: str | None = None) -> dict:
    """The response to an `engine_forkchoiceUpdated` call, against a tree of known payloads."""
    # The execution layer may know a finalized block, the latest one an earlier update named.
    request = {"jsonrpc": "2.0", "id": 1, "method": method, "params": params}
    return _native.engine_forkchoice_updated(tree, finalized, request)


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
    finalized_block_hash: bytes,
    suggested_fee_recipient: bytes,
    target_gas_limit: int,
    verify: bool = True,
    # `Any`, because `dict` is invariant in its values.
    config: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """From Gloas: the forkchoice update and payload attributes of a proposer on a store."""
    # The steps take the form of those of `consensus.fork_choice`, which build the store.
    # The head status is 0 for empty, 1 for full and 2 for pending.
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
        finalized_block_hash,
        suggested_fee_recipient,
        target_gas_limit,
        verify,
        config,
    )


__all__ = [
    "jwt_build",
    "jwt_check",
    "new_payload",
    "new_payload_on_chain",
    "forkchoice_updated",
    "get_blobs",
    "PoolEntry",
    "prepare_execution_payload",
    "prepare_execution_payload_gloas",
    "EngineError",
    "JwtError",
    "ProposerError",
]
