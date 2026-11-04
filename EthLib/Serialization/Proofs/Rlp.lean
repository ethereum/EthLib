module

public import EthLib.Serialization.Proofs.Rlp.Item
public import EthLib.Serialization.Proofs.Rlp.Encode
public import EthLib.Serialization.Proofs.Rlp.Bound
public import EthLib.Serialization.Proofs.Rlp.Strict
public import EthLib.Serialization.Proofs.Rlp.RoundTrip
public import EthLib.Serialization.Proofs.Rlp.Canonical
public import EthLib.Serialization.Proofs.Rlp.Scalar
public import EthLib.Serialization.Proofs.Rlp.Codec

/-!
# `EthLib.Serialization.Proofs.Rlp`

Machine-checked properties of RLP.

- `Proofs/Rlp/Item` proves that `bigEndian` is `BE` of the Yellow Paper.
- `Proofs/Rlp/Encode` proves that `encode` refuses a payload of `2^64` bytes or more.
- `Proofs/Rlp/Bound` proves that `encode` fails exactly on a payload of `2^64` bytes or more.
- `Proofs/Rlp/Strict` proves that `decode` rejects each of the five non-canonical forms, whatever bytes follow.
- `Proofs/Rlp/RoundTrip` proves that decoding undoes encoding, so the encoding is injective and prefix-free.
- `Proofs/Rlp/Canonical` proves that the decoder accepts only canonical input, so `encode` is a bijection onto what `decode` accepts.
- `Proofs/Rlp/Scalar` proves that `decodeScalar` decodes exactly the encodings of scalars, and rejects a leading zero byte.
- `Proofs/Rlp/Codec` proves that each typed codec is lawful.
- So a typed decoder accepts exactly the encoding of a value.
-/
