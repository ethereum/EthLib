"""The exceptions that the specification raises through the bindings."""


# Each primitive has one exception class.
# Each class also derives from `RuntimeError`, `ValueError` or both.
# So a caller can catch a failure with `except ValueError` or `except RuntimeError`.
#
# The Lean type of the error defines the code, one for each constructor.
# A new constructor takes a new code, so that each code keeps its meaning.
#
# Code 0 is a failure that the export reports without a Lean error code.
# Examples are an unknown name, and an input that the export reads before the specification runs.
# No Lean error type uses code 0.
#
# The bindings check the type, the length and the range of some arguments before Lean runs.
# A wrong type raises `TypeError`, and a wrong length `ValueError`.
# An integer out of its range raises `OverflowError`.
# None of them carries a code.
#
# An export of typed values reads its arguments in Lean instead.
# An argument that Lean cannot read raises the error class of the method, with code 0.
# A negative or too large `int`, too many parts or bytes, or deep nesting raises `ValueError`.
# A value of a type that cannot cross, such as a `float` or a `bytearray`, raises `TypeError`.
class EthLibError(Exception):
    """An error of the specification, with its code and its message."""

    code: int
    message: str

    def __init__(self, code: int, message: str) -> None:
        """Keep the code and the message of the Lean error."""
        super().__init__(message)
        self.code = code
        self.message = message


class KzgError(EthLibError, RuntimeError):
    """A KZG operation rejected its input."""


class BlsError(EthLibError, ValueError, RuntimeError):
    """A BLS operation rejected its input."""


class KeyDerivationError(EthLibError, ValueError):
    """Validator key derivation (code 1) or its path (code 2) failed; bad arguments have code 0."""


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


class KeccakError(EthLibError, ValueError):
    """The Keccak-f[1600] permutation rejected its state."""


class EthashError(EthLibError, ValueError):
    """An Ethash export rejected an argument, such as its cache."""


class ReqRespError(EthLibError, ValueError):
    """A request or a response, or a fork name, was rejected."""


class ConsensusError(EthLibError, ValueError):
    """A custody selection failed (codes 1-3), or a name is unknown (code 0)."""


class TransitionError(EthLibError, ValueError):
    """A step of the beacon state transition rejected its state or its block."""


class WeakSubjectivityError(EthLibError, ValueError):
    """The weak subjectivity period or the staleness check of a checkpoint has no answer."""


class ValidatorDutyError(EthLibError, ValueError):
    """A duty of an honest validator has no result for its state or its input."""


class ProposerError(EthLibError, ValueError):
    """A step of an honest proposer has no result for its state or its input."""


class SlashingProtectionError(EthLibError, ValueError):
    """An interchange file does not read, or a signer must refuse a message."""


class LightClientError(EthLibError, ValueError):
    """A light client rejected a bootstrap or an update."""


class ForkChoiceError(EthLibError, ValueError):
    """The fork choice rejected its anchor, or a step could not be read."""


class HkdfError(EthLibError, ValueError):
    """HKDF rejected its input."""


class Pbkdf2Error(EthLibError, ValueError):
    """PBKDF2 rejected its input."""


class ScryptError(EthLibError, ValueError):
    """scrypt or one of its steps rejected its input."""


class ConcatKdfError(EthLibError, ValueError):
    """The Concatenation KDF rejected its input."""


class AesError(EthLibError, ValueError):
    """AES rejected a key or a block size (code 0), or GCM rejected its input (codes 1-6)."""


class BlockError(EthLibError, ValueError):
    """A header, block or receipt was rejected; the code names the failed check."""


class RlpError(EthLibError, ValueError):
    """RLP rejected its input, or no RLP type has the name given."""


class SszError(EthLibError, ValueError):
    """SSZ rejected a type, a value or its bytes, or could not read the JSON of one."""


class SnappyError(EthLibError, ValueError):
    """
    A Snappy block or framed stream was rejected.

    Block errors have codes from 1, and frame errors codes from 101.
    """


class VarintError(EthLibError, ValueError):
    """The bytes are not one minimal varint."""


class GossipError(EthLibError, ValueError):
    """A gossip message was rejected, or its fork has no name."""


class Discv5Error(EthLibError, ValueError):
    """A discv5 input was rejected, with the code of its error, or 0."""


class RlpxError(EthLibError, ValueError):
    """ECIES, the RLPx handshake or RLPx frames rejected its input."""


class Devp2pError(EthLibError, ValueError):
    """A message of the devp2p "p2p" capability was rejected."""


class Discv4Error(EthLibError, ValueError):
    """A discv4 packet was rejected, with the code of its error, or 0 for a bad argument."""


class ForkIdError(EthLibError, ValueError):
    """A node refused the fork identifier of a peer, or an input was malformed, with code 0."""


class EthWireError(EthLibError, ValueError):
    """
    An eth message, a Status or an answer of headers was rejected.

    Message errors have codes from 1, and Status errors codes from 101.

    Header errors have codes from 201, and transaction errors codes from 301.

    A bad argument has code 0.
    """


class SnapError(EthLibError, ValueError):
    """A snap message was rejected, with the code of its error, or 0 for a bad argument."""


class TransactionError(EthLibError, ValueError):
    """A transaction or its network form was rejected, or a fork name is unknown."""


class VrfError(EthLibError, ValueError):
    """A VRF seed was not 32 bytes, with code 0."""


class EvmError(EthLibError, ValueError):
    """An EVM export rejected an argument, an opcode, an immediate byte or a CREATE preimage."""


class FeesError(EthLibError, ValueError):
    """A fee export got an unknown, blobless or unspecified fork, a bad transaction or argument."""


class TrieError(EthLibError, ValueError):
    """
    A trie has no root, a proof does not verify, or an RLP input is malformed.

    Trie errors have codes from 1, proof errors codes from 101, and a malformed input code 0.
    """


class StateError(EthLibError, ValueError):
    """The input of the state root was rejected."""


class PrecompileError(EthLibError, ValueError):
    """
    A precompile call failed, or no precompile has the address.

    The code names the precompile that failed, and code 0 means no precompile has the address.
    """


class EngineError(EthLibError, ValueError):
    """An Engine API method returned a JSON-RPC error, whose code is the negative of this code."""


class ChainError(EthLibError, ValueError):
    """A chain configuration was malformed, with code 0."""


class BindingError(EthLibError, ValueError):
    """An error of an export of typed values, with code 0 when a value does not fit its argument."""


__all__ = [
    "EthLibError",
    "BindingError",
    "KzgError",
    "BlsError",
    "XmssError",
    "SphincsError",
    "Secp256k1Error",
    "Secp256r1Error",
    "EnrError",
    "PrecompileError",
    "StateError",
    "KeccakError",
    "EthashError",
    "ReqRespError",
    "ConsensusError",
    "TransitionError",
    "WeakSubjectivityError",
    "ValidatorDutyError",
    "ProposerError",
    "SlashingProtectionError",
    "LightClientError",
    "ForkChoiceError",
    "HkdfError",
    "Pbkdf2Error",
    "ScryptError",
    "ConcatKdfError",
    "AesError",
    "BlockError",
    "RlpError",
    "SnappyError",
    "SszError",
    "VarintError",
    "GossipError",
    "Discv5Error",
    "RlpxError",
    "Devp2pError",
    "Discv4Error",
    "ForkIdError",
    "EthWireError",
    "SnapError",
    "TransactionError",
    "VrfError",
    "TrieError",
    "EvmError",
    "FeesError",
    "EngineError",
    "ChainError",
]
