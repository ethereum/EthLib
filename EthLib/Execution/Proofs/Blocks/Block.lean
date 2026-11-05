module

public import EthLib.Execution.Blocks.Block
public import EthLib.Execution.Proofs.Blocks.Header
public import EthLib.Execution.Proofs.Blocks.Withdrawal

/-!
# Proofs: blocks

At every fork, the RLP codec of a block is lawful when the codec of its transactions is.

So a block decodes from exactly one byte string, its encoding.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Serialization.Rlp

variable {fork : Fork} {Tx : Type} [Codec Tx] [LawfulCodec Tx]

omit [LawfulCodec Tx] in
/-- The items of a block: the header, the transactions and the ommers, then the withdrawals. -/
theorem Block.toItem_eq (b : Block fork Tx) :
    Codec.toItem b = .list ([Codec.toItem b.header, Codec.toItem b.transactions,
      Codec.toItem b.ommers] ++ Item.ofSince b.withdrawals) := rfl

instance : LawfulCodec (Block fork Tx) where
  ofItem_toItem b := by
    show Block.ofItem (Block.toItem b) = _
    unfold Block.ofItem Block.toItem
    dsimp only
    -- The count of items matches, and each part reads back from its own items.
    rw [Item.fields_list ?count]
    · rw [← List.append_nil (Item.ofSince b.withdrawals)]
      simp only [List.cons_append, List.nil_append, Item.readField_cons, Item.readSince_append,
        bind, Except.bind]
      rfl
    · simp only [List.length_append, List.length_cons, List.length_nil, Item.length_ofSince]
  toItem_of_ofItem {item b} hDecode := by
    change Block.ofItem item = .ok b at hDecode
    unfold Block.ofItem at hDecode
    dsimp only at hDecode
    obtain ⟨items, hFields, hDecode⟩ := bind_ok_iff.mp hDecode
    have hItem := Item.fields_eq_ok.mp hFields
    -- Each read takes the items of one part from the front of the rest.
    iterate 3
      obtain ⟨⟨_, _⟩, hRead, hDecode⟩ := bind_ok_iff.mp hDecode
      have := Item.eq_of_readField hRead
    obtain ⟨⟨_, rest⟩, hRead, hDecode⟩ := bind_ok_iff.mp hDecode
    have := Item.eq_of_readSince hRead
    obtain rfl := Except.ok.inj hDecode
    obtain ⟨rfl, hLen⟩ := hItem
    subst_vars
    -- The parts fill the whole count, so no item is left after the withdrawals.
    simp only [List.length_append, List.length_cons, Item.length_ofSince] at hLen
    obtain rfl : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [Block.toItem_eq]

end EthLib.Execution.Blocks
