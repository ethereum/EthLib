module

public import EthLib.Execution.Blocks.Header
public import EthLib.Execution.Proofs.Trie.Binding
public import EthLib.Serialization.Proofs.Rlp.Codec

/-!
# Proofs: the header of a block

At every fork, the RLP codec of a header is lawful.

So a header decodes from exactly one byte string, its encoding, and the decoder accepts no other.

A header at one fork holds a value in exactly the fields of that fork.

So its RLP list has exactly the count of fields of that fork.

A list with another count never decodes as a header of that fork.

The hash of a decoded header is the hash of the bytes that it decodes from.

Two headers at one fork with one hash are equal.

Otherwise a search returns their encodings, which form a Keccak-256 collision.

Keccak-256 has collisions, so no theorem can rule one out.

The theorems give no bound on the cost of finding one.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Trie (IsCollision)
open EthLib.Serialization.Rlp
open EthLib.Cryptography.Hash.Keccak (keccak256)

variable {fork : Fork}

namespace Header

/-- The items of a header: the 15 fields of Frontier, then the fields added since. -/
theorem toItem_eq (h : Header fork) :
    Codec.toItem h = .list ([Codec.toItem h.parentHash, Codec.toItem h.ommersHash,
      Codec.toItem h.coinbase, Codec.toItem h.stateRoot, Codec.toItem h.transactionsRoot,
      Codec.toItem h.receiptRoot, Codec.toItem h.bloom, Codec.toItem h.difficulty,
      Codec.toItem h.number, Codec.toItem h.gasLimit, Codec.toItem h.gasUsed,
      Codec.toItem h.timestamp, Codec.toItem h.extraData, Codec.toItem h.prevRandao,
      Codec.toItem h.nonce] ++ Item.ofSince h.baseFeePerGas ++ Item.ofSince h.withdrawalsRoot
      ++ Item.ofSince h.blobGasUsed ++ Item.ofSince h.excessBlobGas
      ++ Item.ofSince h.parentBeaconBlockRoot ++ Item.ofSince h.requestsHash
      ++ Item.ofSince h.blockAccessListHash ++ Item.ofSince h.slotNumber) := rfl

/-- The RLP list of a header has one item for each field of its fork. -/
theorem toItem_fields (h : Header fork) :
    ∃ items, Codec.toItem h = .list items ∧ items.length = fieldCount fork := by
  refine ⟨_, toItem_eq h, ?_⟩
  simp only [List.length_append, List.length_cons, List.length_nil, Item.length_ofSince,
    fieldCount]
  omega

end Header

instance : LawfulCodec (Header fork) where
  ofItem_toItem h := by
    show Header.ofItem (Header.toItem h) = _
    unfold Header.ofItem Header.toItem
    dsimp only
    -- The count of items matches, and each field reads back from its own items.
    rw [Item.fields_list ?count]
    · rw [← List.append_nil (Item.ofSince h.slotNumber)]
      simp only [List.append_assoc, List.cons_append, List.nil_append, Item.readField_cons,
        Item.readSince_append, bind, Except.bind]
      rfl
    · simp only [List.length_append, List.length_cons, List.length_nil, Item.length_ofSince,
        Header.fieldCount]
      omega
  toItem_of_ofItem {item h} hDecode := by
    change Header.ofItem item = .ok h at hDecode
    unfold Header.ofItem at hDecode
    dsimp only at hDecode
    obtain ⟨items, hFields, hDecode⟩ := bind_ok_iff.mp hDecode
    have hItem := Item.fields_eq_ok.mp hFields
    -- Each read takes the items of one field from the front of the rest.
    iterate 15
      obtain ⟨⟨_, _⟩, hRead, hDecode⟩ := bind_ok_iff.mp hDecode
      have := Item.eq_of_readField hRead
    iterate 7
      obtain ⟨⟨_, _⟩, hRead, hDecode⟩ := bind_ok_iff.mp hDecode
      have := Item.eq_of_readSince hRead
    obtain ⟨⟨_, rest⟩, hRead, hDecode⟩ := bind_ok_iff.mp hDecode
    have := Item.eq_of_readSince hRead
    obtain rfl := Except.ok.inj hDecode
    obtain ⟨rfl, hLen⟩ := hItem
    subst_vars
    -- The fields fill the whole count, so no item is left after the last one.
    simp only [List.length_append, List.length_cons, Item.length_ofSince, Header.fieldCount]
      at hLen
    obtain rfl : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [Header.toItem_eq]

namespace Header

/-- A decoded header hashes to the Keccak-256 hash of the bytes that it decodes from. -/
theorem hash_of_decode {b : ByteArray} {h : Header fork} (hDecode : Codec.decode b = .ok h) :
    h.hash = .ok (keccak256 b) := by
  simp only [hash, Codec.encode_decode hDecode, bind, Except.bind, pure, Except.pure]
  -- The digest has the 32 bytes of a hash, by the definition of its length.
  rfl

/-- The decoder at a fork rejects a list whose count of items is not the count of that fork. -/
theorem ofItem_wrongFieldCount {items : List Item} (hLen : items.length ≠ fieldCount fork) :
    (Codec.ofItem (.list items) : Except RlpError (Header fork)) =
      .error (.wrongFieldCount (fieldCount fork) items.length) := by
  simp [Codec.ofItem, ofItem, Item.fields, Item.toItems, hLen, bind, Except.bind]

/-- A header hashes to a digest exactly when its encoding hashes to that digest. -/
theorem hash_eq_ok_iff {h : Header fork} {digest : Hash32} :
    h.hash = .ok digest ↔ ∃ bytes, Codec.encode h = .ok bytes ∧ keccak256 bytes = digest := by
  unfold hash
  cases Codec.encode h with
  | error e => simp [bind, Except.bind]
  | ok bytes =>
    constructor
    · intro hh
      exact ⟨bytes, rfl, Except.ok.inj hh⟩
    · rintro ⟨_, hb, rfl⟩
      cases hb
      rfl

/-- The encodings of two headers, when the encodings differ and share one Keccak-256 hash. -/
def findCollision (h₁ h₂ : Header fork) : Option (ByteArray × ByteArray) :=
  match Codec.encode h₁, Codec.encode h₂ with
  | .ok b₁, .ok b₂ => if b₁ ≠ b₂ ∧ keccak256 b₁ = keccak256 b₂ then some (b₁, b₂) else none
  | _, _ => none

/-- Every pair that the search returns holds the two encodings, in order, and is a collision. -/
theorem findCollision_valid {h₁ h₂ : Header fork} {pair : ByteArray × ByteArray}
    (hFound : findCollision h₁ h₂ = some pair) :
    Codec.encode h₁ = .ok pair.1 ∧ Codec.encode h₂ = .ok pair.2 ∧ IsCollision keccak256 pair := by
  unfold findCollision at hFound
  split at hFound
  · rename_i b₁ b₂ hb₁ hb₂
    split at hFound
    · rename_i hcol
      cases hFound
      exact ⟨hb₁, hb₂, hcol⟩
    · cases hFound
  · cases hFound

/-- A header compared with itself has no collision. -/
theorem findCollision_self (h : Header fork) : findCollision h h = none := by
  unfold findCollision
  split
  · rename_i b₁ b₂ hb₁ hb₂
    rw [hb₁] at hb₂
    cases hb₂
    simp
  · rfl

/-- Two headers at one fork with one hash are equal, or the search returns their encodings.

Those encodings then form a Keccak-256 collision. -/
theorem hash_binding {h₁ h₂ : Header fork} {digest : Hash32}
    (hh₁ : h₁.hash = .ok digest) (hh₂ : h₂.hash = .ok digest) :
    h₁ = h₂ ∨ ∃ pair, findCollision h₁ h₂ = some pair ∧
      Codec.encode h₁ = .ok pair.1 ∧ Codec.encode h₂ = .ok pair.2 ∧ IsCollision keccak256 pair := by
  obtain ⟨b₁, hb₁, hk₁⟩ := hash_eq_ok_iff.mp hh₁
  obtain ⟨b₂, hb₂, hk₂⟩ := hash_eq_ok_iff.mp hh₂
  by_cases hne : b₁ = b₂
  · subst hne
    exact .inl (Codec.encode_injective hb₁ hb₂)
  · have hk : keccak256 b₁ = keccak256 b₂ := hk₁.trans hk₂.symm
    refine .inr ⟨(b₁, b₂), ?_, hb₁, hb₂, hne, hk⟩
    simp [findCollision, hb₁, hb₂, hne, hk]

end Header

end EthLib.Execution.Blocks
