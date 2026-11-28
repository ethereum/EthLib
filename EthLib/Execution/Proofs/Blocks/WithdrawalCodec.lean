module

public import EthLib.Execution.Blocks.Withdrawal
public import EthLib.Serialization.Proofs.Rlp.Codec

/-!
# Proofs: the codec of a withdrawal

The RLP codec of a withdrawal is lawful.

So a withdrawal decodes from exactly one byte string, its encoding.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Serialization.Rlp

instance : LawfulCodec Withdrawal where
  ofItem_toItem w := by
    show Withdrawal.ofItem (Withdrawal.toItem w) = _
    simp_record_roundtrip Withdrawal.ofItem Withdrawal.toItem
  toItem_of_ofItem {item w} hDecode := by
    change Withdrawal.ofItem item = .ok w at hDecode
    unfold Withdrawal.ofItem at hDecode
    decode_fields_toItem hDecode 4

end EthLib.Execution.Blocks
