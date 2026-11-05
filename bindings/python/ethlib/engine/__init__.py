"""The Engine API between the consensus and the execution layers."""

import json

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import EngineError
from ethlib.serialization import rlp


def new_payload(config: dict, method: str, params: list) -> dict:
    """The payload status of an `engine_newPayload` call, without the state of the parent."""
    request = {"jsonrpc": "2.0", "id": 1, "method": method, "params": params}
    status = _native.engine_new_payload(json.dumps(config).encode(), json.dumps(request).encode())
    return json.loads(status)


def new_payload_on_chain(
    config: dict, state: bytes, recent: list, method: str, params: list
) -> tuple[dict, bytes | None, list | None]:
    """The payload status of an `engine_newPayload` call, on a chain that holds the parent."""
    # A valid payload also gives its header and the accounts of the state after it.
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
    if header == []:
        return json.loads(status), None, None
    return json.loads(status), rlp.encode(header), accounts


def forkchoice_updated(tree: list, method: str, params: list) -> dict:
    """The response to an `engine_forkchoiceUpdated` call, against a tree of known payloads."""
    request = {"jsonrpc": "2.0", "id": 1, "method": method, "params": params}
    response = _native.engine_forkchoice_updated(
        json.dumps(tree).encode(), json.dumps(request).encode()
    )
    return json.loads(response)


__all__ = ["new_payload", "new_payload_on_chain", "forkchoice_updated", "EngineError"]
