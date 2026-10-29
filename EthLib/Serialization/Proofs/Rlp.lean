import EthLib.Serialization.Proofs.Rlp.Encode

/-!
# `EthLib.Serialization.Proofs.Rlp`

Machine-checked properties of RLP.

`Proofs/Rlp/Encode` checks the encoding against every case of `RLPTests/rlptest.json` in `ethereum/tests`.

It also proves that `encode` refuses a payload of `2^64` bytes or more.
-/
