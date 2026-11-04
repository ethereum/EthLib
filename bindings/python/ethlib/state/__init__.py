"""The state of the execution layer, and the root that commits to it.

A state is given as RLP bytes: a list of accounts.
Each account is the list `[address, nonce, balance, code, storage]`.
The storage is a list of pairs `[key, value]`, with a 32-byte key and a word.
The code hash of an account is the Keccak-256 hash of its code.
"""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ..cryptography import _native


def state_root(state: bytes) -> bytes:
    """The 32-byte state root, with Keccak-256, of the state that the RLP bytes encode.

    A storage key with the value zero is absent from the storage.

    Raises ValueError when the bytes encode no such list, or give one address twice.
    """
    return _native.state_root(state)


__all__ = ["state_root"]
