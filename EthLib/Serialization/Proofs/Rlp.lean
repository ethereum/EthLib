import EthLib.Serialization.Proofs.Rlp.Item
import EthLib.Serialization.Proofs.Rlp.Encode

/-!
# `EthLib.Serialization.Proofs.Rlp`

Machine-checked properties of RLP.

- `Proofs/Rlp/Item` proves that `bigEndian` is `BE` of the Yellow Paper.
- `Proofs/Rlp/Encode` proves that `encode` refuses a payload of `2^64` bytes or more.
- It also checks `encode` against every case of `RLPTests/rlptest.json` in `ethereum/tests`.
-/
