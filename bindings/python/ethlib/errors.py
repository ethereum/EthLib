"""The exceptions that the specification raises through the bindings.

Each primitive has one exception class.
An instance carries the code and the message of the Lean error.
The Lean type of the error defines the code, one for each constructor.
A new constructor takes a new code, so that each code keeps its meaning.

Each class also derives from `RuntimeError`, `ValueError` or both.
So a caller can catch a failure with `except ValueError` or `except RuntimeError`.

Code 0 means a failure that the export reports without a Lean error code.
Examples are an unknown name, and an input that the export reads before the specification runs.
No Lean error type uses code 0.

The bindings check the type and the length of some arguments before Lean runs.
Such a check raises `TypeError` or `ValueError`, with no code.
"""


class EthLibError(Exception):
    """An error of the specification, with its code and its message."""

    code: int
    message: str

    def __init__(self, code: int, message: str) -> None:
        super().__init__(message)
        self.code = code
        self.message = message


class KzgError(EthLibError, RuntimeError):
    """A KZG operation rejected its input."""


class BlsError(EthLibError, ValueError, RuntimeError):
    """A BLS operation rejected its input."""


class XmssError(EthLibError, ValueError, RuntimeError):
    """A leanXMSS operation rejected its input."""


class SphincsError(EthLibError, RuntimeError):
    """A leanSPHINCS operation rejected its input."""


class Secp256k1Error(EthLibError, ValueError):
    """A secp256k1 operation rejected its input."""


class Secp256r1Error(EthLibError, ValueError):
    """secp256r1 verification rejected the bytes of its input."""


class EnrError(EthLibError, ValueError):
    """A node record, or its text form, was rejected."""


class EcrecoverError(EthLibError, ValueError):
    """The ECRECOVER precompile failed."""


class ModexpError(EthLibError, ValueError):
    """The MODEXP precompile failed."""


class Sha256PrecompileError(EthLibError, ValueError):
    """The SHA-256 precompile failed."""


class KeccakError(EthLibError, ValueError):
    """The Keccak-f[1600] permutation rejected its state."""


class ReqRespError(EthLibError, ValueError):
    """A request or a response, or a fork name, was rejected."""


class ConsensusError(EthLibError, ValueError):
    """No preset, configuration or fork has the name given."""


class HkdfError(EthLibError, ValueError):
    """HKDF rejected its input."""


class ConcatKdfError(EthLibError, ValueError):
    """The Concatenation KDF rejected its input."""


class BlockError(EthLibError, ValueError):
    """A header, a block or a receipt was rejected, or no fork has the name given.

    A header or a block has the code of its RLP error, and a receipt error a code from 101.
    """


class RlpError(EthLibError, ValueError):
    """RLP rejected its input, or no RLP type has the name given."""


class SnappyError(EthLibError, ValueError):
    """A Snappy block or framed stream was rejected.

    Block errors have codes from 1, and frame errors codes from 101.
    """


class VarintError(EthLibError, ValueError):
    """The bytes are not one minimal varint."""


class Discv5Error(EthLibError, ValueError):
    """A discv5 input was rejected.

    A packet error has its own code, and any other rejection has code 0.
    """


class RlpxError(EthLibError, ValueError):
    """ECIES rejected its input, or a key or an iv of the binding was rejected with code 0."""


class TransactionError(EthLibError, ValueError):
    """A transaction was rejected, or no fork has the name given."""


class VrfError(EthLibError, ValueError):
    """A VRF seed was not 32 bytes, with code 0."""


class TrieError(EthLibError, ValueError):
    """A trie has no root, a proof does not verify, or an RLP input is malformed.

    Trie errors have codes from 1, proof errors codes from 101, and a malformed input code 0.
    """


class StateError(EthLibError, ValueError):
    """The input of the state root was rejected."""


class PrecompileError(EthLibError, ValueError):
    """A precompile call failed, or no precompile has the address.

    The code names the precompile that failed, and code 0 means no precompile has the address.
    """


__all__ = [
    "EthLibError",
    "KzgError",
    "BlsError",
    "XmssError",
    "SphincsError",
    "Secp256k1Error",
    "Secp256r1Error",
    "EnrError",
    "EcrecoverError",
    "ModexpError",
    "Sha256PrecompileError",
    "PrecompileError",
    "StateError",
    "KeccakError",
    "ReqRespError",
    "ConsensusError",
    "HkdfError",
    "ConcatKdfError",
    "BlockError",
    "RlpError",
    "SnappyError",
    "VarintError",
    "Discv5Error",
    "RlpxError",
    "TransactionError",
    "VrfError",
    "TrieError",
]
