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
    simp only [Withdrawal.ofItem, Withdrawal.toItem, Item.fields, Item.toItems, List.length_cons,
      List.length_nil, ↓reduceIte, Item.readField_cons, bind, Except.bind, pure, Except.pure]
  toItem_of_ofItem {item w} hDecode := by
    change Withdrawal.ofItem item = .ok w at hDecode
    unfold Withdrawal.ofItem at hDecode
    obtain ⟨items, hFields, hDecode⟩ := bind_ok_iff.mp hDecode
    have hItem := Item.fields_eq_ok.mp hFields
    -- Each read takes the item of one field from the front of the rest.
    iterate 4
      obtain ⟨⟨_, _⟩, hRead, hDecode⟩ := bind_ok_iff.mp hDecode
      have := Item.eq_of_readField hRead
    obtain rfl := Except.ok.inj hDecode
    obtain ⟨rfl, hLen⟩ := hItem
    subst_vars
    -- The four fields fill the count, so no item is left.
    simp at hLen
    subst hLen
    rfl

end EthLib.Execution.Blocks
