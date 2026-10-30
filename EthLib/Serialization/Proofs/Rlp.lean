import EthLib.Serialization.Proofs.Rlp.Item
import EthLib.Serialization.Proofs.Rlp.Encode
import EthLib.Serialization.Proofs.Rlp.Bound
import EthLib.Serialization.Proofs.Rlp.Decode
import EthLib.Serialization.Proofs.Rlp.Strict
import EthLib.Serialization.Proofs.Rlp.RoundTrip
import EthLib.Serialization.Proofs.Rlp.Canonical

/-!
# `EthLib.Serialization.Proofs.Rlp`

Machine-checked properties of RLP.

- `Proofs/Rlp/Item` proves that `bigEndian` is `BE` of the Yellow Paper.
- `Proofs/Rlp/Encode` proves that `encode` refuses a payload of `2^64` bytes or more.
- It also checks `encode` against every case of `RLPTests/rlptest.json` in `ethereum/tests`.
- `Proofs/Rlp/Bound` proves that `encode` fails exactly on a payload of `2^64` bytes or more.
- `Proofs/Rlp/Decode` checks `decode` against every case of `rlptest.json` and `invalidRLPTest.json`.
- `Proofs/Rlp/Strict` proves that `decode` rejects each of the five non-canonical forms, whatever bytes follow.
- `Proofs/Rlp/RoundTrip` proves that decoding undoes encoding, so the encoding is injective and prefix-free.
- `Proofs/Rlp/Canonical` proves that the decoder accepts only canonical input, so `encode` is a bijection onto what `decode` accepts.
-/
