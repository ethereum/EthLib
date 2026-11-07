"""The Engine API between the consensus and the execution layers."""

import json

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.consensus import _fork_choice_records
from ethlib.cryptography import _native
from ethlib.errors import EngineError, ProposerError
from ethlib.serialization import rlp


def new_payload(config: dict, method: str, params: list) -> dict:
    """The payload status of an `engine_newPayload` call, without the state of the parent."""
    request = {"jsonrpc": "2.0", "id": 1, "method": method, "params": params}
    status = _native.engine_new_payload(json.dumps(config).encode(), json.dumps(request).encode())
    return json.loads(status)


def new_payload_on_chain(
    config: dict, state: bytes, recent: list, method: str, params: list
) -> tuple[dict, bytes | None, bytes | None]:
    """The payload status of an `engine_newPayload` call, on a chain that holds the parent."""
    # A valid payload also gives the RLP encodings of its header and of the accounts after it.
    request = {"jsonrpc": "2.0", "id": 1, "method": method, "params": params}
    items = [
        [name.encode(), rlp.decode(header), [rlp.decode(o) for o in ommers]]
        for name, header, ommers in recent
    ]
    status, header, accounts = rlp.decode(
        _native.engine_new_payload_on_chain(
            json.dumps(config).encode(), state, rlp.encode(items), json.dumps(request).encode()
        )
    )
    if header == b"":
        return json.loads(status), None, None
    return json.loads(status), header, accounts


def forkchoice_updated(tree: list, method: str, params: list, finalized: str | None = None) -> dict:
    """The response to an `engine_forkchoiceUpdated` call, against a tree of known payloads."""
    # The execution layer may know a finalized block, the latest one an earlier update named.
    request = {"jsonrpc": "2.0", "id": 1, "method": method, "params": params}
    response = _native.engine_forkchoice_updated(
        json.dumps(tree).encode(), json.dumps(finalized).encode(), json.dumps(request).encode()
    )
    return json.loads(response)


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
    replacements = json.dumps(config).encode() if config else b""
    update = _native.engine_prepare_execution_payload(
        name,
        fork,
        state,
        replacements,
        safe_block_hash,
        finalized_block_hash,
        suggested_fee_recipient,
        pow_chain or [],
    )
    return json.loads(update)


def prepare_execution_payload_gloas(
    name: str,
    fork: str,
    anchor_state: bytes,
    anchor_block: bytes,
    steps: list,
    head_root: bytes,
    head_status: int,
    state: bytes,
    safe_block_hash: bytes,
    finalized_block_hash: bytes,
    suggested_fee_recipient: bytes,
    target_gas_limit: int,
    verify: bool = True,
    config: dict | None = None,
) -> dict:
    """From Gloas: the forkchoice update and payload attributes of a proposer on a store."""
    # The steps take the form of those of `consensus.fork_choice`, which build the store.
    # The head status is 0 for empty, 1 for full and 2 for pending.
    replacements = json.dumps(config).encode() if config else b""
    update = _native.engine_prepare_execution_payload_gloas(
        name,
        fork,
        anchor_state,
        anchor_block,
        _fork_choice_records(steps),
        replacements,
        head_root,
        state,
        safe_block_hash,
        finalized_block_hash,
        suggested_fee_recipient,
        head_status,
        target_gas_limit,
        verify,
    )
    return json.loads(update)


__all__ = [
    "new_payload",
    "new_payload_on_chain",
    "forkchoice_updated",
    "prepare_execution_payload",
    "prepare_execution_payload_gloas",
    "EngineError",
    "ProposerError",
]
