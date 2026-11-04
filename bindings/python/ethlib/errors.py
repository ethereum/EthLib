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


class EthashError(EthLibError, ValueError):
    """An Ethash export rejected its cache."""


class ReqRespError(EthLibError, ValueError):
    """A request or a response, or a fork name, was rejected."""


class ConsensusError(EthLibError, ValueError):
    """A custody selection failed (codes 1-3), or a name is unknown (code 0)."""


class HkdfError(EthLibError, ValueError):
    """HKDF rejected its input."""


class ConcatKdfError(EthLibError, ValueError):
    """The Concatenation KDF rejected its input."""


class AesError(EthLibError, ValueError):
    """AES rejected a key or a block size (code 0), or GCM rejected its input (codes 1-6)."""


class BlockError(EthLibError, ValueError):
    """A header, block or receipt was rejected: RLP 1-14, receipts 101-103, checks 201-214."""


class RlpError(EthLibError, ValueError):
    """RLP rejected its input, or no RLP type has the name given."""


class SszError(EthLibError, ValueError):
    """SSZ rejected a type, a value or its bytes, or could not read the JSON of one."""


class SnappyError(EthLibError, ValueError):
    """A Snappy block or framed stream was rejected.

    Block errors have codes from 1, and frame errors codes from 101.
    """


class VarintError(EthLibError, ValueError):
    """The bytes are not one minimal varint."""


class Discv5Error(EthLibError, ValueError):
    """A discv5 input was rejected, with the code of a packet error, a message error, or 0."""


class RlpxError(EthLibError, ValueError):
    """ECIES or the RLPx handshake rejected its input.

    ECIES errors have codes from 1, handshake errors codes from 101, and a bad argument code 0.
    """


class Devp2pError(EthLibError, ValueError):
    """A message of the devp2p "p2p" capability was rejected."""


class Discv4Error(EthLibError, ValueError):
    """A discv4 packet was rejected, with the code of its error, or 0 for a bad argument."""


class TransactionError(EthLibError, ValueError):
    """A transaction or its network form was rejected, or a fork name is unknown."""


class VrfError(EthLibError, ValueError):
    """A VRF seed was not 32 bytes, with code 0."""


class EvmError(EthLibError, ValueError):
    """An opcode does not push a word of its operands alone, with code 0."""


class FeesError(EthLibError, ValueError):
    """A fee export got an unknown fork, or one before Dencun, with code 0."""


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
    "EthashError",
    "ReqRespError",
    "ConsensusError",
    "HkdfError",
    "ConcatKdfError",
    "AesError",
    "BlockError",
    "RlpError",
    "SnappyError",
    "SszError",
    "VarintError",
    "Discv5Error",
    "RlpxError",
    "Devp2pError",
    "Discv4Error",
    "TransactionError",
    "VrfError",
    "TrieError",
    "EvmError",
    "FeesError",
]
