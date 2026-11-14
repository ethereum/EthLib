module

public import EthLib.Execution.Network.Message
public import EthLib.Execution.Proofs.Network.Blocks
public import EthLib.Execution.Proofs.Network.Cells
public import EthLib.Execution.Proofs.Network.Receipts
public import EthLib.Execution.Proofs.Network.Snap
public import EthLib.Execution.Proofs.Network.Status
public import EthLib.Execution.Proofs.Network.Transactions

/-!
# Proofs: the messages of the eth capability

Each message reads back from its ID and its RLP item, on every version that uses its form.

The decoder reads no other ID or item, so it takes no field more or less than the writer writes.

The reader of an envelope reads only that envelope, with or without its part.

eth/68 rejects BlockRangeUpdate.

A version rejects every ID from its count of IDs on as unknown, but not the ID just below it.

Every version rejects an announcement whose lists differ in length.

A response answers a request only when it repeats the request ID.

A BlockHeaders or a PooledTransactions that passes the check of its request answers it.

A Cells response passes its check exactly when it repeats the request ID and its cells pass.

A BlockAccessLists response passes exactly when it repeats the ID and its entries pass.

It must hold one entry for each expected hash.

Each entry must be the empty string, or its RLP encoding must hash to the expected hash there.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Serialization.Rlp

namespace Message

-- The message IDs are numbers, so each case of the decoder is decided by their values.
attribute [local simp] STATUS_ID NEW_BLOCK_HASHES_ID TRANSACTIONS_ID GET_BLOCK_HEADERS_ID
  BLOCK_HEADERS_ID GET_BLOCK_BODIES_ID BLOCK_BODIES_ID NEW_BLOCK_ID
  NEW_POOLED_TRANSACTION_HASHES_ID GET_POOLED_TRANSACTIONS_ID POOLED_TRANSACTIONS_ID
  GET_RECEIPTS_ID RECEIPTS_ID BLOCK_RANGE_UPDATE_ID GET_BLOCK_ACCESS_LISTS_ID BLOCK_ACCESS_LISTS_ID
  GET_CELLS_ID CELLS_ID

/-- The envelope `[request-id, payload]` reads back as its request ID and its payload. -/
theorem readEnvelope_envelope {α : Type} [Codec α] [LawfulCodec α] (i : UInt64) (x : α) :
    readEnvelope (envelope i (Codec.toItem x)) = .ok (i, x) := by
  simp [readEnvelope, envelope, Item.fields, Item.toItems, Item.field_toItem, bind, Except.bind,
    pure, Except.pure]

/-- An item reads as a request ID and a payload exactly when it is their envelope. -/
theorem readEnvelope_eq_ok_iff {α : Type} [Codec α] [LawfulCodec α] {item : Item} {i : UInt64}
    {x : α} : readEnvelope item = .ok (i, x) ↔ item = envelope i (Codec.toItem x) := by
  constructor
  · intro h
    obtain ⟨items, rfl, hlen, hrest⟩ := Item.fields_bind_eq_ok.mp h
    rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> simp at hlen
    obtain ⟨y, rfl, h₁⟩ := Item.field_bind_eq_ok.mp hrest
    obtain ⟨z, rfl, h₂⟩ := Item.field_bind_eq_ok.mp h₁
    cases h₂
    rfl
  · rintro rfl
    exact readEnvelope_envelope i x

/-- A list of items is the item of itself as a list. -/
theorem list_eq_toItem (items : List Item) : Item.list items = Codec.toItem items := by
  show Item.list items = .list (items.map Codec.toItem)
  congr 1
  exact (List.map_id' items).symm

/-- Lists of lists of items are the item of themselves as nested lists. -/
theorem lists_eq_toItem (lists : List (List Item)) :
    Item.list (lists.map .list) = Codec.toItem lists := by
  show Item.list (lists.map .list) = .list (lists.map Codec.toItem)
  congr 1
  apply List.map_congr_left
  intro l _
  exact list_eq_toItem l

/-- The envelope of a version reads back as its request ID, its part and its payload.

This needs the part to be present exactly from eth/70 on. -/
theorem readWithPart_withPart {α β : Type} [Codec α] [LawfulCodec α] [Codec β] [LawfulCodec β]
    {version : EthVersion} (i : UInt64) (part : Option α) (x : β)
    (h : part.isSome ↔ EthVersion.eth70 ≤ version) :
    readWithPart version (withPart i part (Codec.toItem x)) = .ok (i, part, x) := by
  cases part with
  | none =>
    have hv : version < .eth70 := by
      simp at h
      exact Nat.lt_of_not_le h
    simp [readWithPart, withPart, hv, readEnvelope_envelope, bind, Except.bind, pure, Except.pure]
  | some p =>
    have hv : ¬ version < .eth70 := by
      simp at h
      exact Nat.not_lt_of_le h
    simp [readWithPart, withPart, hv, Item.fields, Item.toItems, Item.field_toItem, bind,
      Except.bind, pure, Except.pure]

/-- An item reads as a request ID, a part and a payload exactly when it is their envelope.

The part is present exactly from eth/70 on. -/
theorem readWithPart_eq_ok_iff {α β : Type} [Codec α] [LawfulCodec α] [Codec β] [LawfulCodec β]
    {version : EthVersion} {item : Item} {i : UInt64} {part : Option α} {x : β} :
    readWithPart version item = .ok (i, part, x) ↔
      (part.isSome ↔ EthVersion.eth70 ≤ version) ∧ item = withPart i part (Codec.toItem x) := by
  constructor
  · intro h
    unfold readWithPart at h
    split at h
    · rename_i hv
      obtain ⟨⟨j, y⟩, hy, h⟩ := bind_ok_iff.mp h
      cases h
      refine ⟨?_, readEnvelope_eq_ok_iff.mp hy⟩
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
      exact Nat.not_le_of_lt hv
    · rename_i hv
      obtain ⟨items, rfl, hlen, hrest⟩ := Item.fields_bind_eq_ok.mp h
      rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at hlen
      obtain ⟨y, rfl, h₁⟩ := Item.field_bind_eq_ok.mp hrest
      obtain ⟨z, rfl, h₂⟩ := Item.field_bind_eq_ok.mp h₁
      obtain ⟨w, rfl, h₃⟩ := Item.field_bind_eq_ok.mp h₂
      cases h₃
      exact ⟨iff_of_true rfl (Nat.le_of_not_lt hv), rfl⟩
  · rintro ⟨hv, rfl⟩
    exact readWithPart_withPart i part x hv

/-- A message has the form of a version.

Status and announcements have the form of their version.

An announcement has as many types and sizes as hashes.

BlockRangeUpdate exists from eth/69 on, and the receipt messages carry their part from eth/70 on.

The other messages have one form at every version. -/
def FitsVersion (version : EthVersion) : Message → Prop
  | .status (.eth68 ..) => version = .eth68
  | .status (.eth69 ..) => version ≠ .eth68
  | .blockRangeUpdate _ => EthVersion.eth69 ≤ version
  | .newPooledTransactionHashes a@(.eth68 ..) => version < .eth72 ∧ a.lengthsAgree
  | .newPooledTransactionHashes a@(.eth72 ..) => version = .eth72 ∧ a.lengthsAgree
  | .getReceipts _ k _ => (k.isSome ↔ EthVersion.eth70 ≤ version)
  | .receipts _ b _ => (b.isSome ↔ EthVersion.eth70 ≤ version)
  | .getBlockAccessLists .. | .blockAccessLists .. => EthVersion.eth71 ≤ version
  | .getCells .. | .cells .. => EthVersion.eth72 ≤ version
  | _ => True

/-- A message of the form of a version reads back from its ID and its item on that version. -/
theorem ofItem_toItem {version : EthVersion} {m : Message} (hm : m.FitsVersion version) :
    ofItem version m.id m.toItem = .ok m := by
  cases m with
  | status s =>
    cases s with
    | eth68 v n td h g id =>
      subst hm
      simp [ofItem, Message.id, toItem, Status.ofItem_eth68, Functor.map, Except.map,
        Except.mapError]
    | eth69 v n g id r =>
      simp [ofItem, Message.id, toItem, Status.ofItem_eth69 hm, Functor.map, Except.map,
        Except.mapError]
  | blockRangeUpdate r =>
    have hm : EthVersion.eth69 ≤ version := hm
    simp [ofItem, Message.id, toItem, hm, LawfulCodec.ofItem_toItem, Functor.map, Except.map,
      Except.mapError]
  | newBlockHashes bs =>
    simp [ofItem, Message.id, toItem, LawfulCodec.ofItem_toItem, Functor.map, Except.map,
      Except.mapError]
  | transactions txs =>
    simp [ofItem, Message.id, toItem, list_eq_toItem txs, LawfulCodec.ofItem_toItem,
      Functor.map, Except.map, Except.mapError]
  | getBlockHeaders i r =>
    simp [ofItem, Message.id, toItem, readEnvelope_envelope, Functor.map, Except.map,
      Except.mapError]
  | blockHeaders i hs =>
    simp [ofItem, Message.id, toItem, list_eq_toItem hs, readEnvelope_envelope, Functor.map,
      Except.map, Except.mapError]
  | getBlockBodies i hs =>
    simp [ofItem, Message.id, toItem, readEnvelope_envelope, Functor.map, Except.map,
      Except.mapError]
  | blockBodies i bs =>
    simp [ofItem, Message.id, toItem, list_eq_toItem bs, readEnvelope_envelope, Functor.map,
      Except.map, Except.mapError]
  | newBlock b td =>
    simp [ofItem, Message.id, toItem, Item.fields, Item.toItems, Item.field_toItem, bind,
      Except.bind, pure, Except.pure, Except.mapError]
  | newPooledTransactionHashes a =>
    cases a with
    | eth68 t sz h =>
      obtain ⟨hv, hl⟩ := hm
      simp [ofItem, Message.id, toItem, Announcement.ofItem_eth68 hv, hl, Except.mapError, bind,
        Except.bind, pure, Except.pure]
    | eth72 t sz h c =>
      obtain ⟨rfl, hl⟩ := hm
      simp [ofItem, Message.id, toItem, Announcement.ofItem_eth72, hl, Except.mapError, bind,
        Except.bind, pure, Except.pure]
  | getPooledTransactions i hs =>
    simp [ofItem, Message.id, toItem, readEnvelope_envelope, Functor.map, Except.map,
      Except.mapError]
  | pooledTransactions i txs =>
    simp [ofItem, Message.id, toItem, list_eq_toItem txs, readEnvelope_envelope, Functor.map,
      Except.map, Except.mapError]
  | getReceipts i k hs =>
    simp [ofItem, Message.id, toItem, readWithPart_withPart i k hs hm, Functor.map, Except.map,
      Except.mapError]
  | receipts i b ls =>
    simp [ofItem, Message.id, toItem, lists_eq_toItem ls, readWithPart_withPart i b ls hm,
      Functor.map, Except.map, Except.mapError]
  | getBlockAccessLists i hs =>
    have hm : EthVersion.eth71 ≤ version := hm
    simp [ofItem, Message.id, toItem, hm, readEnvelope_envelope, Functor.map, Except.map,
      Except.mapError]
  | blockAccessLists i ls =>
    have hm : EthVersion.eth71 ≤ version := hm
    simp [ofItem, Message.id, toItem, hm, list_eq_toItem ls, readEnvelope_envelope, Functor.map,
      Except.map, Except.mapError]
  | getCells i hs m =>
    have hm : EthVersion.eth72 ≤ version := hm
    have h71 : EthVersion.eth71 ≤ version := Nat.le_trans (by decide) hm
    simp [ofItem, Message.id, toItem, hm, h71, Item.fields, Item.toItems, Item.field_toItem,
      bind, Except.bind, pure, Except.pure, Except.mapError]
  | cells i hs gs m =>
    have hm : EthVersion.eth72 ≤ version := hm
    have h71 : EthVersion.eth71 ≤ version := Nat.le_trans (by decide) hm
    simp [ofItem, Message.id, toItem, hm, h71, Item.fields, Item.toItems, Item.field_toItem,
      bind, Except.bind, pure, Except.pure, Except.mapError]

/-- A message reads exactly from its own ID and its item, on a version that uses its form.

So the decoder takes no item with fields missing or added, and no message of another version.

It takes no announcement whose lists differ in length. -/
theorem ofItem_eq_ok_iff {version : EthVersion} {id : Nat} {item : Item} {m : Message} :
    ofItem version id item = .ok m ↔ id = m.id ∧ m.FitsVersion version ∧ item = m.toItem := by
  constructor
  · intro h
    unfold ofItem at h
    by_cases hc : id = STATUS_ID
    · rw [ite_eq_left hc] at h
      obtain ⟨s, hs, rfl⟩ := map_ok_iff.mp (mapError_ok_iff.mp h)
      obtain ⟨rfl, hv⟩ := Status.ofItem_eq_ok_iff.mp hs
      refine ⟨hc, ?_, rfl⟩
      cases s <;> exact hv
    rw [ite_eq_right hc] at h
    by_cases hc : id = NEW_BLOCK_HASHES_ID
    · rw [ite_eq_left hc] at h
      obtain ⟨bs, hb, rfl⟩ := map_ok_iff.mp (mapError_ok_iff.mp h)
      exact ⟨hc, trivial, (Codec.ofItem_eq_ok_iff.mp hb).symm⟩
    rw [ite_eq_right hc] at h
    by_cases hc : id = TRANSACTIONS_ID
    · rw [ite_eq_left hc] at h
      obtain ⟨txs, hb, rfl⟩ := map_ok_iff.mp (mapError_ok_iff.mp h)
      exact ⟨hc, trivial, ((list_eq_toItem txs).trans (Codec.ofItem_eq_ok_iff.mp hb)).symm⟩
    rw [ite_eq_right hc] at h
    by_cases hc : id = GET_BLOCK_HEADERS_ID
    · rw [ite_eq_left hc] at h
      obtain ⟨⟨i, r⟩, hr, rfl⟩ := map_ok_iff.mp (mapError_ok_iff.mp h)
      exact ⟨hc, trivial, readEnvelope_eq_ok_iff.mp hr⟩
    rw [ite_eq_right hc] at h
    by_cases hc : id = BLOCK_HEADERS_ID
    · rw [ite_eq_left hc] at h
      obtain ⟨⟨i, hs⟩, hr, rfl⟩ := map_ok_iff.mp (mapError_ok_iff.mp h)
      refine ⟨hc, trivial, ?_⟩
      show item = envelope i (.list hs)
      rw [list_eq_toItem hs]
      exact readEnvelope_eq_ok_iff.mp hr
    rw [ite_eq_right hc] at h
    by_cases hc : id = GET_BLOCK_BODIES_ID
    · rw [ite_eq_left hc] at h
      obtain ⟨⟨i, hs⟩, hr, rfl⟩ := map_ok_iff.mp (mapError_ok_iff.mp h)
      exact ⟨hc, trivial, readEnvelope_eq_ok_iff.mp hr⟩
    rw [ite_eq_right hc] at h
    by_cases hc : id = BLOCK_BODIES_ID
    · rw [ite_eq_left hc] at h
      obtain ⟨⟨i, bs⟩, hr, rfl⟩ := map_ok_iff.mp (mapError_ok_iff.mp h)
      refine ⟨hc, trivial, ?_⟩
      show item = envelope i (.list bs)
      rw [list_eq_toItem bs]
      exact readEnvelope_eq_ok_iff.mp hr
    rw [ite_eq_right hc] at h
    by_cases hc : id = NEW_BLOCK_ID
    · rw [ite_eq_left hc] at h
      obtain ⟨items, rfl, hlen, hrest⟩ := Item.fields_bind_eq_ok.mp (mapError_ok_iff.mp h)
      rcases items with _ | ⟨b, _ | ⟨td, _ | ⟨_, _⟩⟩⟩ <;> simp at hlen
      obtain ⟨n, rfl, h₁⟩ := Item.field_bind_eq_ok.mp hrest
      cases h₁
      exact ⟨hc, trivial, rfl⟩
    rw [ite_eq_right hc] at h
    by_cases hc : id = NEW_POOLED_TRANSACTION_HASHES_ID
    · rw [ite_eq_left hc] at h
      obtain ⟨a, ha, h₁⟩ := bind_ok_iff.mp h
      obtain ⟨rfl, hv⟩ := Announcement.ofItem_eq_ok_iff.mp (mapError_ok_iff.mp ha)
      cases hl : a.lengthsAgree
      · cases a <;> simp [Announcement.lists, hl, throw, throwThe, MonadExceptOf.throw] at h₁
      · cases a <;> simp [hl, pure, Except.pure] at h₁ <;> subst h₁ <;>
          exact ⟨hc, ⟨hv, hl⟩, rfl⟩
    rw [ite_eq_right hc] at h
    by_cases hc : id = GET_POOLED_TRANSACTIONS_ID
    · rw [ite_eq_left hc] at h
      obtain ⟨⟨i, hs⟩, hr, rfl⟩ := map_ok_iff.mp (mapError_ok_iff.mp h)
      exact ⟨hc, trivial, readEnvelope_eq_ok_iff.mp hr⟩
    rw [ite_eq_right hc] at h
    by_cases hc : id = POOLED_TRANSACTIONS_ID
    · rw [ite_eq_left hc] at h
      obtain ⟨⟨i, txs⟩, hr, rfl⟩ := map_ok_iff.mp (mapError_ok_iff.mp h)
      refine ⟨hc, trivial, ?_⟩
      show item = envelope i (.list txs)
      rw [list_eq_toItem txs]
      exact readEnvelope_eq_ok_iff.mp hr
    rw [ite_eq_right hc] at h
    by_cases hc : id = GET_RECEIPTS_ID
    · rw [ite_eq_left hc] at h
      obtain ⟨⟨i, k, hs⟩, hr, rfl⟩ := map_ok_iff.mp (mapError_ok_iff.mp h)
      obtain ⟨hk, rfl⟩ := readWithPart_eq_ok_iff.mp hr
      exact ⟨hc, hk, rfl⟩
    rw [ite_eq_right hc] at h
    by_cases hc : id = RECEIPTS_ID
    · rw [ite_eq_left hc] at h
      obtain ⟨⟨i, b, ls⟩, hr, rfl⟩ := map_ok_iff.mp (mapError_ok_iff.mp h)
      obtain ⟨hb, hi⟩ := readWithPart_eq_ok_iff.mp hr
      refine ⟨hc, hb, ?_⟩
      show item = withPart i b (.list (ls.map .list))
      rw [lists_eq_toItem ls]
      exact hi
    rw [ite_eq_right hc] at h
    by_cases hc : id = GET_BLOCK_ACCESS_LISTS_ID ∧ EthVersion.eth71 ≤ version
    · rw [ite_eq_left hc] at h
      obtain ⟨⟨i, hs⟩, hr, rfl⟩ := map_ok_iff.mp (mapError_ok_iff.mp h)
      exact ⟨hc.1, hc.2, readEnvelope_eq_ok_iff.mp hr⟩
    rw [ite_eq_right hc] at h
    by_cases hc : id = BLOCK_ACCESS_LISTS_ID ∧ EthVersion.eth71 ≤ version
    · rw [ite_eq_left hc] at h
      obtain ⟨⟨i, ls⟩, hr, rfl⟩ := map_ok_iff.mp (mapError_ok_iff.mp h)
      refine ⟨hc.1, hc.2, ?_⟩
      show item = envelope i (.list ls)
      rw [list_eq_toItem ls]
      exact readEnvelope_eq_ok_iff.mp hr
    rw [ite_eq_right hc] at h
    by_cases hc : id = GET_CELLS_ID ∧ EthVersion.eth72 ≤ version
    · rw [ite_eq_left hc] at h
      obtain ⟨items, rfl, hlen, hrest⟩ := Item.fields_bind_eq_ok.mp (mapError_ok_iff.mp h)
      rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at hlen
      obtain ⟨i, rfl, h₁⟩ := Item.field_bind_eq_ok.mp hrest
      obtain ⟨hs, rfl, h₂⟩ := Item.field_bind_eq_ok.mp h₁
      obtain ⟨mask, rfl, h₃⟩ := Item.field_bind_eq_ok.mp h₂
      cases h₃
      exact ⟨hc.1, hc.2, rfl⟩
    rw [ite_eq_right hc] at h
    by_cases hc : id = CELLS_ID ∧ EthVersion.eth72 ≤ version
    · rw [ite_eq_left hc] at h
      obtain ⟨items, rfl, hlen, hrest⟩ := Item.fields_bind_eq_ok.mp (mapError_ok_iff.mp h)
      rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at hlen
      obtain ⟨i, rfl, h₁⟩ := Item.field_bind_eq_ok.mp hrest
      obtain ⟨hs, rfl, h₂⟩ := Item.field_bind_eq_ok.mp h₁
      obtain ⟨gs, rfl, h₃⟩ := Item.field_bind_eq_ok.mp h₂
      obtain ⟨mask, rfl, h₄⟩ := Item.field_bind_eq_ok.mp h₃
      cases h₄
      exact ⟨hc.1, hc.2, rfl⟩
    rw [ite_eq_right hc] at h
    by_cases hc : id = BLOCK_RANGE_UPDATE_ID ∧ EthVersion.eth69 ≤ version
    · rw [ite_eq_left hc] at h
      obtain ⟨r, hr, rfl⟩ := map_ok_iff.mp (mapError_ok_iff.mp h)
      exact ⟨hc.1, hc.2, (Codec.ofItem_eq_ok_iff.mp hr).symm⟩
    rw [ite_eq_right hc] at h
    cases h
  · rintro ⟨rfl, hm, rfl⟩
    exact ofItem_toItem hm

/-- eth/68 rejects BlockRangeUpdate, which eth/69 adds. -/
theorem ofItem_blockRangeUpdate_eth68 (item : Item) :
    ofItem .eth68 BLOCK_RANGE_UPDATE_ID item = .error (.unknownId BLOCK_RANGE_UPDATE_ID) := by
  have : ¬ EthVersion.eth69 ≤ .eth68 := by decide
  simp [ofItem, this]

/-- A reader refuses an announcement whose types and sizes are not as many as its hashes. -/
theorem ofItem_unequalLengths {version : EthVersion} {a : Announcement}
    (hv : Announcement.ofItem version a.toItem = .ok a) (hl : a.lengthsAgree = false) :
    ofItem version NEW_POOLED_TRANSACTION_HASHES_ID a.toItem
      = .error (.unequalLengths a.lists.1.size a.lists.2.1.length a.lists.2.2.length) := by
  simp [ofItem, hv, hl, Except.mapError, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- A version rejects every ID from `n` on as unknown exactly when its count of IDs is at most `n`.

So the count of IDs of a version is the first ID from which every ID is unknown to it. -/
theorem messageCount_le_iff_unknownId {version : EthVersion} {n : Nat} :
    version.messageCount ≤ n ↔
      ∀ id, n ≤ id → ∀ item, ofItem version id item = .error (.unknownId id) := by
  constructor
  · intro h id hid item
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_trans h hid)
    cases version <;> simp +arith +decide [ofItem, EthVersion.messageCount]
  · intro h
    refine Nat.not_lt.mp fun hlt => ?_
    have last (m : Message) (hm : m.FitsVersion version) (hid : m.id = version.messageCount - 1) :
        False := by
      have := h m.id (by omega) m.toItem
      rw [ofItem_toItem hm] at this
      cases this
    cases version
    · exact last (.receipts 0 none []) (by simp +decide [FitsVersion]) rfl
    · exact last (.blockRangeUpdate ⟨0, 0, default⟩) (by simp +decide [FitsVersion]) rfl
    · exact last (.blockRangeUpdate ⟨0, 0, default⟩) (by simp +decide [FitsVersion]) rfl
    · exact last (.blockAccessLists 0 []) (by simp +decide [FitsVersion]) rfl
    · exact last (.cells 0 [] [] default) (by simp +decide [FitsVersion]) rfl

/-- A response that answers a request is a response with the request ID of the request. -/
theorem requestId_of_answers {request response : Message} (h : answers request response) :
    ∃ i, request.requestId? = some i ∧ response.requestId? = some i := by
  cases request <;> cases response <;> simp_all [answers, requestId?]

/-- Every response type answers its request type when it repeats the request ID. -/
theorem answers_of_requestId (i : UInt64) (r : HeaderRequest) (hs : List Item)
    (hashes : List Hash32) (bs txs : List Item) (k : Option Nat) (b : Option Bool)
    (ls : List (List Item)) :
    answers (getBlockHeaders i r) (blockHeaders i hs) ∧
      answers (getBlockBodies i hashes) (blockBodies i bs) ∧
      answers (getPooledTransactions i hashes) (pooledTransactions i txs) ∧
      answers (getReceipts i k hashes) (receipts i b ls) := by
  simp [answers]

/-- A response of headers that passes the check answers the request, with its request ID. -/
theorem answers_of_checkHeaderResponse {request response : Message}
    (h : checkHeaderResponse request response = .ok ()) : answers request response := by
  unfold checkHeaderResponse at h
  split at h
  · rename_i i r j hs
    by_cases hij : i = j
    · simp [answers, hij]
    · simp [hij, throw, throwThe, MonadExceptOf.throw] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A response of transactions that passes the check answers the request, with its request ID. -/
theorem answers_of_checkPooledResponse {request response : Message}
    (h : checkPooledResponse request response = .ok ()) : answers request response := by
  unfold checkPooledResponse at h
  split at h
  · rename_i i hs j txs
    by_cases hij : i = j
    · simp [answers, hij]
    · simp [hij, throw, throwThe, MonadExceptOf.throw] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A response passes the check of cells exactly when two conditions hold.

The request is GetCells, and the response is Cells with its request ID.

The cells of the response pass the check against the hashes and the bitmap of the request.

That check also reads the number of blobs of each transaction, which the caller gives. -/
theorem checkCellsResponse_eq_ok_iff {blobs : List Nat} {request response : Message} :
    checkCellsResponse blobs request response = .ok () ↔
      ∃ i requested requestMask hashes groups mask,
        request = getCells i requested requestMask ∧ response = cells i hashes groups mask ∧
          checkCells requested requestMask blobs hashes groups mask = .ok () := by
  unfold checkCellsResponse
  split
  · rename_i i requested requestMask j hashes groups mask
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, getCells.injEq, cells.injEq]
      constructor
      · intro h
        exact ⟨i, requested, requestMask, hashes, groups, mask, ⟨rfl, rfl, rfl⟩,
          ⟨rfl, rfl, rfl, rfl⟩, h⟩
      · rintro ⟨_, _, _, _, _, _, ⟨rfl, rfl, rfl⟩, ⟨-, rfl, rfl, rfl⟩, h⟩
        exact h
    · simp only [hij, ↓reduceIte, throw, throwThe, MonadExceptOf.throw, getCells.injEq,
        cells.injEq]
      constructor
      · intro h
        nomatch h
      · rintro ⟨_, _, _, _, _, _, ⟨rfl, -, -⟩, ⟨h, -⟩, -⟩
        exact absurd h.symm hij
  · rename_i hne
    simp only [throw, throwThe, MonadExceptOf.throw]
    constructor
    · intro h
      nomatch h
    · rintro ⟨i, requested, requestMask, hashes, groups, mask, rfl, rfl, -⟩
      exact absurd rfl (hne i requested requestMask i hashes groups mask rfl)

/-- A response passes the check of access lists exactly when three conditions hold.

The request is GetBlockAccessLists, and the response is BlockAccessLists with its request ID.

The response has one entry for each expected hash.

Each entry is the empty string, or its RLP encoding hashes to the expected hash at its position. -/
theorem accessListsResponse_eq_true_iff {expected : List Hash32} {request response : Message} :
    accessListsResponse expected request response = true ↔
      ∃ i hashes lists, request = getBlockAccessLists i hashes ∧
        response = blockAccessLists i lists ∧ lists.length = expected.length ∧
          ∀ (k : Nat) (hk : k < lists.length) (he : k < expected.length),
            lists[k] = .bytes .empty ∨
              ∃ bytes, Serialization.Rlp.encode lists[k] = .ok bytes ∧
                Cryptography.Hash.Keccak.keccak256 bytes = expected[k] := by
  unfold accessListsResponse
  split
  · rename_i i hashes j lists
    simp only [Bool.and_eq_true, beq_iff_eq, accessListsAnswer_eq_true_iff,
      getBlockAccessLists.injEq, blockAccessLists.injEq]
    constructor
    · rintro ⟨⟨rfl, hlen⟩, -, H⟩
      exact ⟨i, hashes, lists, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, hlen, H⟩
    · rintro ⟨_, _, _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, hlen, H⟩
      exact ⟨⟨rfl, hlen⟩, by omega, H⟩
  · rename_i hne
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    rintro i hashes lists rfl rfl
    exact absurd rfl (hne i hashes i lists rfl)

end Message

/-- Two errors with one code come from one constructor. -/
theorem EthError.code_injective (e₁ e₂ : EthError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [EthError.code] at h; exact absurd h (by decide))

end EthLib.Execution.Network
