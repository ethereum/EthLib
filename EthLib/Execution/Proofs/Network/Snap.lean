module

public import EthLib.Execution.Network.Snap
public import EthLib.Execution.Proofs.Network.Protocol
public import EthLib.Execution.Proofs.Network.Status
public import EthLib.Execution.Proofs.Trie.HexPrefix
public import EthLib.Serialization.Proofs.Rlp.Encodings
import EthLib.Base.Proofs.CodeInjective

/-!
# Proofs: the snap capability

Each message reads back from its ID and its RLP item on the versions that use its ID.

The decoder reads no other ID or item, so it takes no field more or less than the writer writes.

The codes and the access lists of a checked answer are the requested ones.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Serialization.Rlp

/-- An entry reads back from its item, for an account body and for slot data alike. -/
instance {α : Type} [Codec α] [LawfulCodec α] : LawfulCodec (RangeEntry α) where
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
  by_cases hr : root = Trie.emptyTrieRoot Cryptography.Hash.Keccak.keccak256 <;>
    by_cases hc : code = State.EMPTY_CODE_HASH <;>
    simp [ofSlimAccount, slimAccount, hr, hc, toItem_hash_ne_empty, Item.fields, Item.toItems,
      Item.field_toItem, bind, Except.bind, pure, Except.pure]

/-- The slim form converts to the full encoding of its account. -/
theorem fullAccount_slimAccount {account : State.Account} {root : Hash32} {full : ByteArray}
    (hfull : State.encodeAccount account root = .ok full) :
    fullAccount (slimAccount account root) = some full := by
  simp [fullAccount, ofSlimAccount_slimAccount, hfull, Except.toOption]

/-- A byte string is never the body of an account, whatever bytes it holds. -/
theorem fullAccount_bytes (bytes : ByteArray) : fullAccount (.bytes bytes) = none := by
  simp [fullAccount, ofSlimAccount, Item.fields, Item.toItems, bind, Except.bind]

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
theorem messageCount_ne_zero (v : SnapVersion) : v.messageCount ≠ 0 := by
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
private theorem SNAP_NAME_ne_ETH_NAME : SNAP_NAME ≠ ETH_NAME := by
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
      exact SnapVersion.messageCount_ne_zero v
  next hname =>
    -- A snap capability has another name.
    have hsnap : ¬∃ v : SnapVersion, v.capability = c := by
      rintro ⟨v, rfl⟩
      exact hname rfl
    simp only [hsnap, false_or]
    exact ethLength_ne_zero_iff

namespace SnapMessage

/-- Each access list of a message keeps the bytes of its own encoding. -/
def Kept (m : SnapMessage) : Prop :=
  ∀ e ∈ m.kept, Serialization.Rlp.encode e.item = .ok e.bytes

/-- A message whose ID the version uses reads back from its ID and its item.

Its access lists must keep their own encodings, and `data` must encode its item. -/
theorem ofItem_toItem {version : SnapVersion} {m : SnapMessage} {data : ByteArray}
    (hm : usesId version m.id) (hk : m.Kept) (hd : Serialization.Rlp.encode m.toItem = .ok data) :
    ofItem version m.id m.toItem data = .ok m := by
  cases m
  case blockAccessLists i ls =>
    -- The encodings cut from the payload are those that the access lists keep.
    obtain ⟨payload, hp, hpe⟩ := payloadEncodings_of_encode hd
    obtain ⟨encodings, hl, hz⟩ :=
      bind_ok_iff.mp ((zip_listEncodings_eq_ok_iff hp).mpr ⟨rfl, hk⟩)
    simp_all [ofItem, SnapMessage.id, toItem, Item.toItems, Item.field_toItem, bind,
      Except.bind, pure, Except.pure, Except.mapError]
  all_goals
    simp_all [ofItem, SnapMessage.id, toItem, Item.toItems, Item.field_toItem, bind,
      Except.bind, pure, Except.pure, Except.mapError]

/-- A message reads exactly from its own ID and its item, on a version that uses its ID.

So the decoder takes no item other than the one the writer writes, and no ID of another version.

When `data` encodes the item, each access list keeps its own encoding. -/
theorem ofItem_eq_ok_iff {version : SnapVersion} {id : Nat} {item : Item} {data : ByteArray}
    {m : SnapMessage} (hd : Serialization.Rlp.encode item = .ok data) :
    ofItem version id item data = .ok m ↔
      id = m.id ∧ usesId version m.id ∧ item = m.toItem ∧ m.Kept := by
  constructor
  · intro h
    unfold ofItem at h
    by_cases hu : usesId version id = true
    · simp only [hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      rw [mapError_ok_iff, bind_ok_iff] at h
      obtain ⟨items, hitems, h⟩ := h
      obtain rfl := Item.toItems_eq_ok.mp hitems
      split at h
      case h_10 i ls =>
        -- Each access list is paired with its own encoding, cut from the payload.
        obtain ⟨_, rfl, h₁⟩ := Item.field_bind_eq_ok.mp h
        obtain ⟨lists, hls, h₂⟩ := bind_ok_iff.mp h₁
        obtain rfl := Item.toItems_eq_ok.mp (mapError_ok_iff.mp hls)
        obtain ⟨encodings, hl, h₃⟩ := bind_ok_iff.mp h₂
        obtain ⟨kept, hz, h₄⟩ := bind_ok_iff.mp h₃
        cases h₄
        obtain ⟨payload, hp, hpe⟩ := payloadEncodings_of_encode hd
        obtain ⟨rfl, hk⟩ :=
          (zip_listEncodings_eq_ok_iff (kept := kept) hp).mp
            (by simp [← hpe, hl, bind, Except.bind, hz])
        exact ⟨rfl, hu, rfl, hk⟩
      all_goals
        repeat
          rw [Item.field_bind_eq_ok] at h
          obtain ⟨_, rfl, h⟩ := h
        cases h
        all_goals exact ⟨rfl, hu, rfl, by simp [Kept, kept]⟩
    · simp [hu, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · rintro ⟨rfl, hm, rfl, hk⟩
    exact ofItem_toItem hm hk hd

/-- A message that the decoder reads from `data` encodes back to exactly `data`.

The RLP decoder takes only canonical input, and the message keeps its whole item. -/
theorem encode_of_decode {version : SnapVersion} {id : Nat} {data : ByteArray} {m : SnapMessage}
    (h : decode version id data = .ok m) : m.encode = .ok data := by
  unfold decode at h
  cases hd : Serialization.Rlp.decode data with
  | error e => simp [hd, Except.mapError, bind, Except.bind] at h
  | ok item =>
    simp only [hd, Except.mapError, bind, Except.bind] at h
    obtain ⟨-, -, rfl, -⟩ := (ofItem_eq_ok_iff (encode_decode data _ hd)).mp h
    simp [encode, encode_decode data _ hd, Except.mapError]

/-- Each access list that the decoder reads from `data` keeps the bytes of its encoding.

So its hash reads those bytes, and no caller has to encode it again. -/
theorem kept_of_decode {version : SnapVersion} {id : Nat} {data : ByteArray} {m : SnapMessage}
    (h : decode version id data = .ok m) : m.Kept := by
  unfold decode at h
  cases hd : Serialization.Rlp.decode data with
  | error e => simp [hd, Except.mapError, bind, Except.bind] at h
  | ok item =>
    simp only [hd, Except.mapError, bind, Except.bind] at h
    -- The data is the encoding of the item, so the reader pairs each list with its encoding.
    exact ((ofItem_eq_ok_iff (encode_decode data _ hd)).mp h).2.2.2

/-- snap/2 rejects GetTrieNodes and TrieNodes, which it removes. -/
theorem ofItem_snap2_trieNodes (item : Item) (data : ByteArray) :
    ofItem .snap2 0x06 item data = .error (.unknownId 0x06) ∧
      ofItem .snap2 0x07 item data = .error (.unknownId 0x07) := by
  simp [ofItem, usesId, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- snap/1 rejects GetBlockAccessLists and BlockAccessLists, which snap/2 adds. -/
theorem ofItem_snap1_accessLists (item : Item) (data : ByteArray) :
    ofItem .snap1 0x08 item data = .error (.unknownId 0x08) ∧
      ofItem .snap1 0x09 item data = .error (.unknownId 0x09) := by
  simp [ofItem, usesId, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- A version rejects every ID from `n` on as unknown exactly when its count of IDs is at most `n`.

So the count of IDs of a version is the first ID from which every ID is unknown to it. -/
theorem messageCount_le_iff_unknownId {version : SnapVersion} {n : Nat} :
    version.messageCount ≤ n ↔
      ∀ id, n ≤ id → ∀ item data, ofItem version id item data = .error (.unknownId id) := by
  constructor
  · intro h id hid item data
    have hu : usesId version id = false := by
      cases version <;> simp [usesId, SnapVersion.messageCount] at h ⊢ <;> omega
    simp [ofItem, hu, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · intro h
    refine Nat.not_lt.mp fun hlt => ?_
    have last (m : SnapMessage) (hm : usesId version m.id) (hk : m.Kept)
        (hm' : ∃ data, Serialization.Rlp.encode m.toItem = .ok data)
        (hid : m.id = version.messageCount - 1) : False := by
      obtain ⟨data, hd⟩ : ∃ data, Serialization.Rlp.encode m.toItem = .ok data := hm'
      have := h m.id (by omega) m.toItem data
      rw [ofItem_toItem hm hk hd] at this
      cases this
    cases version
    · exact last (.trieNodes 0 []) (by decide) (by simp [Kept, kept]) ⟨_, rfl⟩ rfl
    · exact last (.blockAccessLists 0 []) (by decide) (by simp [Kept, kept]) ⟨_, rfl⟩ rfl

/-- A response that answers a request repeats its request ID. -/
theorem requestId_of_answers {request response : SnapMessage}
    (h : answers request response = true) : request.requestId = response.requestId := by
  cases request <;> cases response <;> simp_all [answers, requestId]

end SnapMessage

/-- Two errors with one code come from one constructor. -/
theorem SnapError.code_injective (e₁ e₂ : SnapError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  code_injective SnapError.code

/-- The codes of a checked answer hash to requested hashes, in the order of the request. -/
theorem sublist_of_codesAnswer {requested : List Hash32} {codes : List ByteArray}
    (h : codesAnswer requested codes) :
    (codes.map Cryptography.Hash.Keccak.keccak256).Sublist requested :=
  List.isSublist_iff_sublist.mp h

/-- An answer of access lists passes the check exactly when two conditions hold.

It holds no more entries than there are expected hashes.

Each entry is the empty string, or the bytes it was read from hash to the expected hash there.

A decoded answer keeps the encoding of each entry as those bytes. -/
theorem accessListsAnswer_eq_true_iff {expected : List Hash32} {lists : List Encoded} :
    accessListsAnswer expected lists = true ↔
      lists.length ≤ expected.length ∧
        ∀ (i : Nat) (hi : i < lists.length) (he : i < expected.length),
          lists[i].item = .bytes .empty ∨
            Cryptography.Hash.Keccak.keccak256 lists[i].bytes = expected[i] := by
  simp only [accessListsAnswer, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine and_congr_right fun hlen => ?_
  rw [List.forall_mem_iff_forall_getElem]
  simp only [List.length_zip, List.getElem_zip, Bool.or_eq_true, beq_iff_eq]
  refine ⟨fun H i hi he => ?_, fun H i hi => ?_⟩
  · rcases H i (by omega) with h | h
    · exact .inl h
    · exact .inr (eq_of_beq h)
  · rcases H i (by omega) (by omega) with h | h
    · exact .inl h
    · right
      rw [h]
      exact beq_self_eq_true _

/-- Each access list of a checked answer is absent, or hashes to the access list hash of its block.

That block is the one at its position. -/
theorem of_accessListsAnswer {expected : List Hash32} {lists : List Encoded}
    (h : accessListsAnswer expected lists) :
    lists.length ≤ expected.length ∧
      ∀ (i : Nat) (hi : i < lists.length) (he : i < expected.length),
        lists[i].item = .bytes .empty ∨
          Cryptography.Hash.Keccak.keccak256 lists[i].bytes = expected[i] :=
  accessListsAnswer_eq_true_iff.mp h

/-! ## Trie node paths -/

/-- A path of 32 bytes reads as its 64 nibbles. -/
theorem readPath_full {bytes : ByteArray} (h : bytes.size = 32) :
    readPath bytes = .ok (Trie.bytesToNibbleList bytes) := by
  simp [readPath, h]

/-- A compact path of fewer than 32 bytes reads as the nibbles it encodes, whatever its flag. -/
theorem readPath_compact (path : TriePath) (isLeaf : Bool)
    (h : (Trie.nibbleListToCompact path isLeaf).size < 32) :
    readPath (Trie.nibbleListToCompact path isLeaf) = .ok path := by
  simp [readPath, Nat.ne_of_lt h, h, Trie.compactToNibbleList_nibbleListToCompact]

/-- A group read from a list of paths asks for one node per path after the first.

A list of one path asks for one node. -/
theorem nodeCount_readGroup {paths : List ByteArray} {group : PathGroup}
    (h : readGroup paths = .ok group) : nodeCount [group] = max 1 (paths.length - 1) := by
  rcases paths with _ | ⟨account, _ | ⟨slot, more⟩⟩
  · cases h
  · simp only [readGroup] at h
    cases hr : readPath account <;>
      simp [hr, bind, Except.bind, pure, Except.pure] at h
    subst h
    simp [nodeCount]
  · simp only [readGroup] at h
    cases ha : readPath account <;> cases hs : readPath slot <;>
      cases hm : more.mapM readPath <;>
      simp [ha, hs, hm, bind, Except.bind, pure, Except.pure] at h
    subst h
    simp [nodeCount, mapM_ok_length hm]

/-- The lists of paths read as one group each, in order. -/
theorem length_readGroups {paths : List (List ByteArray)} {groups : List PathGroup}
    (h : readGroups paths = .ok groups) : groups.length = paths.length :=
  mapM_ok_length h

/-- Every prefix of an accepted TrieNodes answer is accepted. -/
theorem trieNodesAnswer_take {groups : List PathGroup} {nodes : List ByteArray}
    (h : trieNodesAnswer groups nodes = true) (n : Nat) :
    trieNodesAnswer groups (nodes.take n) = true := by
  simp only [trieNodesAnswer, decide_eq_true_eq, List.length_take] at h ⊢
  omega

end EthLib.Execution.Network
