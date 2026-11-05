module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Blocks.Block
public import EthLib.Execution.Proofs.Blocks.Header
public import EthLib.Execution.Proofs.Blocks.Withdrawal

/-!
# Proofs: blocks

At every fork, a block reads back from its RLP item when each ommer has the fork of its number.

That holds when the codec of its transactions is lawful.

An item that decodes as a block is the item of that block.

Each ommer that the decoder returns has the fork of its own number.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Serialization.Rlp

variable {fork : Fork} {Tx : Type} [Codec Tx] [LawfulCodec Tx]

namespace Header

/-- The number read from the item of a header is the number of the header. -/
theorem numberOfItem_toItem {f : Fork} (h : Header f) :
    numberOfItem (Codec.toItem h) = .ok h.number := by
  simp [numberOfItem, toItem_eq, NUMBER_FIELD, Item.toItems, Item.field,
    LawfulCodec.ofItem_toItem, Except.mapError, bind, Except.bind]

/-- A header reads back with the fork of its number, when that is its own fork. -/
theorem ofItemAtNumber_toItem (forkOf : Nat → Fork) (ommer : (f : Fork) × Header f)
    (hFork : ommer.1 = forkOf ommer.2.number) :
    ofItemAtNumber forkOf (Codec.toItem ommer.2) = .ok ommer := by
  obtain ⟨f, h⟩ := ommer
  simp only [ofItemAtNumber, numberOfItem_toItem, bind, Except.bind, pure, Except.pure]
  generalize forkOf h.number = g at hFork ⊢
  subst hFork
  simp [LawfulCodec.ofItem_toItem]

/-- A header read with the fork of its number has that fork, and its item is the item read. -/
theorem ofItemAtNumber_eq_ok {forkOf : Nat → Fork} {item : Item}
    {ommer : (f : Fork) × Header f} (hDecode : ofItemAtNumber forkOf item = .ok ommer) :
    Codec.toItem ommer.2 = item ∧ ommer.1 = forkOf ommer.2.number := by
  unfold ofItemAtNumber at hDecode
  obtain ⟨number, hNumber, hDecode⟩ := bind_ok_iff.mp hDecode
  obtain ⟨h, hHeader, hDecode⟩ := bind_ok_iff.mp hDecode
  obtain rfl := (Except.ok.inj hDecode).symm
  have hItem := LawfulCodec.toItem_of_ofItem hHeader
  refine ⟨hItem, ?_⟩
  -- The number read from the item is the number of the header that the item holds.
  rw [← hItem, numberOfItem_toItem] at hNumber
  exact congrArg forkOf (Except.ok.inj hNumber).symm

end Header

omit [LawfulCodec Tx] in
/-- The items of a block: the header, the transactions and the ommers, then the withdrawals. -/
theorem Block.toItem_eq (b : Block fork Tx) :
    b.toItem = .list ([Codec.toItem b.header, Codec.toItem b.transactions,
      ommersItem b.ommers] ++ Item.ofSince b.withdrawals) := rfl

/-- A block reads back from its item when each ommer has the fork of its own number. -/
theorem Block.ofItem_toItem (forkOf : Nat → Fork) (b : Block fork Tx)
    (hOmmers : ∀ ommer ∈ b.ommers, ommer.1 = forkOf ommer.2.number) :
    Block.ofItem forkOf b.toItem = .ok b := by
  -- The ommers are the item of a list of items.
  have hItems : ommersItem b.ommers =
      Codec.toItem (b.ommers.map fun ommer => Codec.toItem ommer.2 : List Item) := by
    simp [ommersItem, Codec.toItem]
  unfold Block.ofItem Block.toItem
  dsimp only
  rw [hItems]
  -- Each ommer reads back from its own item.
  have hMap : (b.ommers.map fun ommer => Codec.toItem ommer.2).mapM
      (Header.ofItemAtNumber forkOf) = .ok b.ommers := by
    rw [List.mapM_map]
    simpa using mapM_eq_ok_map (g := id) (f := Header.ofItemAtNumber forkOf ∘ _)
      fun ommer hm => Header.ofItemAtNumber_toItem forkOf ommer (hOmmers ommer hm)
  -- The count of items matches, and each part reads back from its own items.
  rw [Item.fields_list ?count]
  · rw [← List.append_nil (Item.ofSince b.withdrawals)]
    simp only [List.cons_append, List.nil_append, Item.readField_cons, Item.readSince_append,
      hMap, Except.mapError, bind, Except.bind]
    rfl
  · simp only [List.length_append, List.length_cons, List.length_nil, Item.length_ofSince]

/-- An item that decodes as a block is the item of that block. -/
theorem Block.toItem_of_ofItem {forkOf : Nat → Fork} {item : Item} {b : Block fork Tx}
    (hDecode : Block.ofItem forkOf item = .ok b) : b.toItem = item := by
  unfold Block.ofItem at hDecode
  dsimp only at hDecode
  obtain ⟨items, hFields, hDecode⟩ := bind_ok_iff.mp hDecode
  have hItem := Item.fields_eq_ok.mp hFields
  -- Each read takes the items of one part from the front of the rest.
  iterate 3
    obtain ⟨⟨_, _⟩, hRead, hDecode⟩ := bind_ok_iff.mp hDecode
    have := Item.eq_of_readField hRead
  obtain ⟨ommers, hOmmers, hDecode⟩ := bind_ok_iff.mp hDecode
  obtain ⟨⟨_, rest⟩, hRead, hDecode⟩ := bind_ok_iff.mp hDecode
  have := Item.eq_of_readSince hRead
  obtain rfl := Except.ok.inj hDecode
  obtain ⟨rfl, hLen⟩ := hItem
  subst_vars
  -- The parts fill the whole count, so no item is left after the withdrawals.
  simp only [List.length_append, List.length_cons, Item.length_ofSince] at hLen
  obtain rfl : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
  -- Each ommer is the header of its own item.
  have hMap := map_of_mapM_ok (p := fun ommer => Codec.toItem ommer.2) (q := id)
    (fun _ _ h => (Header.ofItemAtNumber_eq_ok h).1) (mapError_ok_iff.mp hOmmers)
  have hList (l : List Item) : (Codec.toItem l : Item) = .list l := by simp [Codec.toItem]
  simp [Block.toItem_eq, ommersItem, hMap, hList]

omit [LawfulCodec Tx] in
/-- Each ommer of a decoded block has the fork of its own number. -/
theorem Block.ommer_fork_of_ofItem {forkOf : Nat → Fork} {item : Item} {b : Block fork Tx}
    (hDecode : Block.ofItem forkOf item = .ok b) :
    ∀ ommer ∈ b.ommers, ommer.1 = forkOf ommer.2.number := by
  unfold Block.ofItem at hDecode
  dsimp only at hDecode
  obtain ⟨_, -, hDecode⟩ := bind_ok_iff.mp hDecode
  iterate 3
    obtain ⟨⟨_, _⟩, -, hDecode⟩ := bind_ok_iff.mp hDecode
  obtain ⟨ommers, hOmmers, hDecode⟩ := bind_ok_iff.mp hDecode
  obtain ⟨⟨_, _⟩, -, hDecode⟩ := bind_ok_iff.mp hDecode
  obtain rfl := Except.ok.inj hDecode
  intro ommer hm
  obtain ⟨_, -, h⟩ := mapM_ok_mem (mapError_ok_iff.mp hOmmers) ommer hm
  exact (Header.ofItemAtNumber_eq_ok h).2

end EthLib.Execution.Blocks
