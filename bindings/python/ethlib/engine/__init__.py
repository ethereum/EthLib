"""The Engine API between the consensus and the execution layers."""

import json

from ..errors import EngineError

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ..cryptography import _native


def new_payload(config: dict, method: str, params: list) -> dict:
    """The payload status of an `engine_newPayload` call, without the state of the parent."""
    request = {"jsonrpc": "2.0", "id": 1, "method": method, "params": params}
    status = _native.engine_new_payload(json.dumps(config).encode(), json.dumps(request).encode())
    return json.loads(status)


__all__ = ["new_payload", "EngineError"]
