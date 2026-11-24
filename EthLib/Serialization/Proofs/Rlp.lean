module

public import EthLib.Serialization.Proofs.Rlp.Item
public import EthLib.Serialization.Proofs.Rlp.Bytes
public import EthLib.Serialization.Proofs.Rlp.Loops
public import EthLib.Serialization.Proofs.Rlp.Encode
public import EthLib.Serialization.Proofs.Rlp.Bound
public import EthLib.Serialization.Proofs.Rlp.Strict
public import EthLib.Serialization.Proofs.Rlp.RoundTrip
public import EthLib.Serialization.Proofs.Rlp.Canonical
public import EthLib.Serialization.Proofs.Rlp.Scalar
public import EthLib.Serialization.Proofs.Rlp.Codec
public import EthLib.Serialization.Proofs.Rlp.Encodings

/-!
# Proofs of RLP

This module gathers the machine-checked properties of RLP.

- `Proofs/Rlp/Item` proves that the big-endian bytes of the code are `BE` of the Yellow Paper.
- `Proofs/Rlp/Bytes` sees the bytes that the decoder reads between two positions as a list.
- `Proofs/Rlp/Loops` restates the loops of the encoder and the decoder as plain recursions.
- `Proofs/Rlp/Encode` proves that the encoder refuses a payload of `2^64` bytes or more.
- `Proofs/Rlp/Bound` proves that the encoder fails exactly on a payload of `2^64` bytes or more.
- `Proofs/Rlp/Strict` proves that the decoder rejects each of the five non-canonical forms.
  It rejects them whatever bytes follow.
- `Proofs/Rlp/RoundTrip` proves that decoding undoes encoding.
  So the encoding is injective and prefix-free.
- `Proofs/Rlp/Canonical` proves that the decoder accepts only canonical input.
  So the encoder is a bijection onto what the decoder accepts.
- `Proofs/Rlp/Scalar` proves that the scalar decoder decodes exactly the encodings of scalars.
  It rejects a leading zero byte.
- `Proofs/Rlp/Encodings` proves that the encoding of a list splits into the encodings of its items.
- `Proofs/Rlp/Codec` proves that each typed codec is lawful.
- So a typed decoder accepts exactly the encoding of a value.
-/
