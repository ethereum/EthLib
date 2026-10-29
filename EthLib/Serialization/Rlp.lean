import EthLib.Serialization.Rlp.Item
import EthLib.Serialization.Rlp.Encode

/-!
# `EthLib.Serialization.Rlp`

Recursive Length Prefix (RLP) is the serialization of the execution layer.

Appendix B of the Yellow Paper (Shanghai version) defines it.

That is `Paper.tex` in `ethereum/yellowpaper` at commit `efc5f9a1f356cba376c978eedb63cb0363c2aa85`.

```text
    Rlp/Item     items, the errors, and the bytes of a scalar
    Rlp/Encode   the encoding
```

The properties proved of these definitions sit under `EthLib.Serialization.Proofs.Rlp`, mirroring this layout.
-/
