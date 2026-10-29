import EthLib.Serialization.Rlp.Item
import EthLib.Serialization.Rlp.Encode

/-!
# `EthLib.Serialization.Rlp`

Recursive Length Prefix (RLP) is the serialization of the execution layer.

Appendix B of the Yellow Paper (Shanghai version) defines it.

```text
    Rlp/Item     items, the errors, and the bytes of a scalar
    Rlp/Encode   the encoding
```

The properties proved of these definitions sit under `EthLib.Serialization.Proofs.Rlp`, mirroring this layout.
-/
