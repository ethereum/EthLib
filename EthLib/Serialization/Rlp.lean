import EthLib.Serialization.Rlp.Item
import EthLib.Serialization.Rlp.Encode

/-!
# `EthLib.Serialization.Rlp`

Recursive Length Prefix (RLP), the serialization of the execution layer.

Source: Appendix B of the Yellow Paper, Shanghai version, in [`Paper.tex` at `efc5f9a`](https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex).

- `Rlp/Item` holds the items, the errors, and the big-endian bytes of a number.
- `Rlp/Encode` holds the encoding.

The properties proved of these definitions sit under `EthLib.Serialization.Proofs.Rlp`, mirroring this layout.
-/
