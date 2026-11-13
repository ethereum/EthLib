"""The execution JSON-RPC API: its parameter readers, error codes, and a chain that serves it."""

from collections.abc import Sequence
from dataclasses import dataclass
from typing import Any, Literal, TypeAlias, overload

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import RpcError

# An error code as the extension carries it: whether it is negative, then its absolute value.
# The extension carries only integers that are not negative, so a code crosses with its sign.
_SignedCode: TypeAlias = tuple[bool, int]

# A tag that names a block by its role.
BlockTag: TypeAlias = Literal["earliest", "finalized", "safe", "latest", "pending"]

# A block parameter: a number, a tag, or a hash with the flag that the block be canonical.
BlockParam: TypeAlias = (
    tuple[Literal["number"], int]
    | tuple[Literal["tag"], BlockTag]
    | tuple[Literal["hash"], bytes, bool]
)

# The schemas of the source whose values read as an `int`.
NumberSchema: TypeAlias = Literal["byte", "uint", "uint32", "uint64", "uint256", "uintDecimal"]

# The schemas of the source whose values read as `bytes`.
# A storage slot of type `bytesMax32` reads as its 32 bytes.
BytesSchema: TypeAlias = Literal[
    "bytes",
    "bytesMax32",
    "bytes4",
    "bytes8",
    "bytes16",
    "bytes32",
    "bytes48",
    "bytes65",
    "bytes96",
    "bytes256",
    "hash32",
    "address",
]

# The schemas of the source of a block parameter.
BlockSchema: TypeAlias = Literal[
    "BlockNumberOrTag", "BlockNumberOrTagForRange", "BlockNumberOrTagOrHash"
]

# Every schema that the reader knows.
Schema: TypeAlias = NumberSchema | BytesSchema | BlockSchema


@dataclass(frozen=True, slots=True, kw_only=True)
class ErrorCode:
    """An error code of the execution JSON-RPC API, with the message that its group gives it."""

    code: int
    message: str


@dataclass(frozen=True, slots=True, kw_only=True)
class ErrorGroup:
    """A group of error codes, with the least and the greatest code it declares, if any."""

    name: str
    range: tuple[int, int] | None
    errors: tuple[ErrorCode, ...]


@overload
def read_param(schema: NumberSchema, value: object) -> int: ...
@overload
def read_param(schema: BytesSchema, value: object) -> bytes: ...
@overload
def read_param(schema: BlockSchema, value: object) -> BlockParam: ...
@overload
def read_param(schema: Schema, value: object) -> int | bytes | BlockParam: ...
def read_param(schema: Schema, value: object) -> int | bytes | BlockParam:
    """
    Read the JSON value of a parameter, as `json.loads` gives it, under a schema of the API.

    A value that the schema rejects raises RpcError with code 32602, and the reason as message.
    An unknown schema raises RpcError with code 0.
    """
    return _native.rpc_read_param(schema, value)


def _code(signed: _SignedCode) -> int:
    negative, magnitude = signed
    return -magnitude if negative else magnitude


def _error_code(entry: tuple[_SignedCode, str]) -> ErrorCode:
    code, message = entry
    return ErrorCode(code=_code(code), message=message)


def error_groups() -> tuple[ErrorGroup, ...]:
    """The groups of error codes of the execution JSON-RPC API, in the order of the source."""
    # The two groups of JSON-RPC itself declare no range.
    return tuple(
        ErrorGroup(
            name=name,
            range=None if bounds is None else (_code(bounds[0]), _code(bounds[1])),
            errors=tuple(_error_code(entry) for entry in errors),
        )
        for name, bounds, errors in _native.rpc_error_groups()
    )


def pruned_history_unavailable() -> ErrorCode:
    """The code of history that the node pruned, which many methods list outside every group."""
    return _error_code(_native.rpc_pruned_history_unavailable())


# A block of a chain: the name of its fork, then its RLP form.
ChainBlock: TypeAlias = tuple[str, bytes]


def serve(
    config: dict[str, Any],
    state: bytes,
    blocks: Sequence[ChainBlock],
    forkchoice: tuple[bytes, bytes, bytes],
    network_id: int,
    requests: list[str],
    *,
    check_seal: bool = True,
) -> list[str | None]:
    """
    Answer the texts of JSON-RPC requests from a chain, with the text of each response.

    A notification, or a batch of notifications, gets None.

    The chain is its configuration, the state of its first block, and its blocks in order.
    Each later block runs through the state transition, which checks the seal if check_seal is set.
    The forkchoice is the head, safe and finalized hashes; a zero safe or finalized hash names none.
    A block that does not decode or fails its transition raises RpcError with its block error code.
    Any other bad input raises RpcError with code 0, such as a head that is not the last block.

    For eth_config, config may give mergeForkBlock, the FORK_NEXT_VALUE of EIP-3675.
    When the first block is not block zero, eth_config needs genesisHash and genesisTime in config.
    When it is block zero, serve reads both from it, and any given values must match.
    A malformed, partial or mismatched value of these keys raises RpcError with code 0.
    """
    view = (config, state, list(blocks), forkchoice, network_id, check_seal)
    return _native.rpc_serve(view, requests)


__all__ = [
    "BlockParam",
    "BlockSchema",
    "BlockTag",
    "BytesSchema",
    "ChainBlock",
    "ErrorCode",
    "ErrorGroup",
    "NumberSchema",
    "RpcError",
    "Schema",
    "error_groups",
    "pruned_history_unavailable",
    "read_param",
    "serve",
]
