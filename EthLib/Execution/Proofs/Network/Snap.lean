module

public import EthLib.Execution.Network.Snap
public import EthLib.Execution.Proofs.Network.Protocol
public import EthLib.Execution.Proofs.Network.Status

/-!
# Proofs: the snap capability

A snap version and its number determine each other.

The count of message IDs for snap and eth is nonzero exactly on the capabilities of their versions.

An account reads back from its slim form.

Each message reads back from its ID and its RLP item on the versions that use its ID.

snap/2 rejects the trie node messages of snap/1, and snap/1 the access list messages of snap/2.

The codes and the access lists of a checked answer are the requested ones.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Serialization.Rlp

instance : LawfulCodec RangeEntry where
  ofItem_toItem e := by
    show RangeEntry.ofItem (RangeEntry.toItem e) = _
    simp only [RangeEntry.ofItem, RangeEntry.toItem, Item.fields, Item.toItems, List.length_cons,
      List.length_nil, ↓reduceIte, Item.field_toItem, bind, Except.bind, pure, Except.pure]
  toItem_of_ofItem {item e} h := by
    change RangeEntry.ofItem item = .ok e at h
    unfold RangeEntry.ofItem at h
    obtain ⟨items, rfl, hlen, hrest⟩ := Item.fields_bind_eq_ok.mp h
    rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> simp at hlen
    obtain ⟨x, rfl, h1⟩ := Item.field_bind_eq_ok.mp hrest
    obtain ⟨y, rfl, h2⟩ := Item.field_bind_eq_ok.mp h1
    cases h2
    rfl

/-- The item of a 32-byte hash is never the empty string. -/
theorem toItem_hash_ne_empty (h : Hash32) : (Codec.toItem h : Item) ≠ .bytes .empty := by
  intro he
  have := congrArg (fun i => match i with | Item.bytes b => b.size | _ => 0) he
  simp [Codec.toItem, ByteArray.size] at this

/-- An account and its storage root read back from the slim form. -/
theorem ofSlimAccount_slimAccount (account : State.Account) (root : Hash32) :
    ofSlimAccount (slimAccount account root) = .ok (account, root) := by
  obtain ⟨nonce, balance, code⟩ := account
  by_cases hr : root = EMPTY_TRIE_ROOT <;> by_cases hc : code = State.EMPTY_CODE_HASH <;>
    simp [ofSlimAccount, slimAccount, hr, hc, toItem_hash_ne_empty, Item.fields, Item.toItems,
      Item.field_toItem, bind, Except.bind, pure, Except.pure]

namespace SnapVersion

/-- The number of a version reads back to that version. -/
theorem ofNumber?_number (v : SnapVersion) : ofNumber? v.number = some v := by
  cases v <;> rfl

/-- A number reads to a version exactly when it is the number of that version. -/
theorem ofNumber?_eq_some_iff {n : Nat} {v : SnapVersion} :
    ofNumber? n = some v ↔ v.number = n := by
  constructor
  · intro h
    unfold ofNumber? at h
    split at h <;> cases h <;> rfl
  · rintro rfl
    exact ofNumber?_number v

/-- Two versions with one number are one version. -/
theorem number_injective : Function.Injective number := fun a b h => by
  have := ofNumber?_number a
  rwa [h, ofNumber?_number, Option.some.injEq, eq_comm] at this

/-- Every snap version has at least one message ID. -/
theorem messageCount_pos (v : SnapVersion) : 0 < v.messageCount := by
  cases v <;> decide

end SnapVersion

/-- The multiplexing of RLPx gives a snap capability the message count of its version. -/
theorem capabilityLength_snap (v : SnapVersion) :
    capabilityLength v.capability = v.messageCount := by
  cases v <;> rfl

/-- The multiplexing of RLPx gives an eth capability the message count of its version. -/
theorem capabilityLength_eth (v : EthVersion) :
    capabilityLength v.capability = v.messageCount := by
  cases v <;> rfl

/-- The names of the two capabilities differ. -/
theorem SNAP_NAME_ne_ETH_NAME : SNAP_NAME ≠ ETH_NAME := by
  decide

/-- The snap and eth count of message IDs is nonzero exactly on a snap or an eth capability. -/
theorem capabilityLength_ne_zero_iff {c : Networking.Devp2p.Capability} :
    capabilityLength c ≠ 0 ↔
      (∃ v : SnapVersion, v.capability = c) ∨ ∃ v : EthVersion, v.capability = c := by
  unfold capabilityLength
  split
  next hname =>
    -- An eth capability has another name.
    have heth : ¬∃ v : EthVersion, v.capability = c := by
      rintro ⟨v, rfl⟩
      exact SNAP_NAME_ne_ETH_NAME hname.symm
    simp only [heth, or_false]
    constructor
    · intro h
      cases hv : SnapVersion.ofNumber? c.version with
      | none => simp [hv] at h
      | some v =>
        refine ⟨v, ?_⟩
        cases c
        simp only [SnapVersion.capability, Networking.Devp2p.Capability.mk.injEq]
        exact ⟨hname.symm, SnapVersion.ofNumber?_eq_some_iff.mp hv⟩
    · rintro ⟨v, rfl⟩
      simp only [SnapVersion.capability, SnapVersion.ofNumber?_number, Option.map_some,
        Option.getD_some]
      exact Nat.pos_iff_ne_zero.mp (SnapVersion.messageCount_pos v)
  next hname =>
    -- A snap capability has another name.
    have hsnap : ¬∃ v : SnapVersion, v.capability = c := by
      rintro ⟨v, rfl⟩
      exact hname rfl
    simp only [hsnap, false_or]
    exact ethLength_ne_zero_iff

namespace SnapMessage

/-- A message whose ID the version uses reads back from its ID and its item. -/
theorem ofItem_toItem {version : SnapVersion} {m : SnapMessage} (hm : usesId version m.id) :
    ofItem version m.id m.toItem = .ok m := by
  cases m <;>
    simp_all [ofItem, SnapMessage.id, toItem, Item.toItems, Item.field_toItem, bind,
      Except.bind, pure, Except.pure, Except.mapError]

/-- snap/2 rejects GetTrieNodes and TrieNodes, which it removes. -/
theorem ofItem_snap2_trieNodes (item : Item) :
    ofItem .snap2 0x06 item = .error (.unknownId 0x06) ∧
      ofItem .snap2 0x07 item = .error (.unknownId 0x07) := by
  simp [ofItem, usesId, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- snap/1 rejects GetBlockAccessLists and BlockAccessLists, which snap/2 adds. -/
theorem ofItem_snap1_accessLists (item : Item) :
    ofItem .snap1 0x08 item = .error (.unknownId 0x08) ∧
      ofItem .snap1 0x09 item = .error (.unknownId 0x09) := by
  simp [ofItem, usesId, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- A response that answers a request repeats its request ID. -/
theorem requestId_of_answers {request response : SnapMessage}
    (h : answers request response = true) : request.requestId = response.requestId := by
  cases request <;> cases response <;> simp_all [answers, requestId]

end SnapMessage

/-- Two errors with one code come from one constructor. -/
theorem SnapError.code_injective (e₁ e₂ : SnapError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [SnapError.code] at h; exact absurd h (by decide))

/-- The codes of a checked answer hash to requested hashes, in the order of the request. -/
theorem sublist_of_codesAnswer {requested : List Hash32} {codes : List ByteArray}
    (h : codesAnswer requested codes) :
    (codes.map Cryptography.Hash.Keccak.keccak256).Sublist requested :=
  List.isSublist_iff_sublist.mp h

/-- Each access list of a checked answer is absent, or hashes to the access list hash of its block.

That block is the one at its position. -/
theorem of_accessListsAnswer {expected : List Hash32} {lists : List Item}
    (h : accessListsAnswer expected lists) :
    lists.length ≤ expected.length ∧
      ∀ (i : Nat) (hi : i < lists.length) (he : i < expected.length),
        lists[i] = .bytes .empty ∨
          ∃ bytes, Serialization.Rlp.encode lists[i] = .ok bytes ∧
            Cryptography.Hash.Keccak.keccak256 bytes = expected[i] := by
  simp only [accessListsAnswer, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  refine ⟨hlen, fun i hi he => ?_⟩
  have hmem : (lists[i], expected[i]) ∈ lists.zip expected :=
    List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩
  have := hall _ hmem
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with he' | henc
  · exact .inl he'
  · right
    cases hb : Serialization.Rlp.encode lists[i] with
    | error e => simp [hb] at henc
    | ok bytes =>
      simp only [hb] at henc
      exact ⟨bytes, rfl, eq_of_beq henc⟩

end EthLib.Execution.Network
