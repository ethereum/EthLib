module

public import EthLib.Execution.Network.Message
public import EthLib.Execution.Proofs.Network.Blocks
public import EthLib.Execution.Proofs.Network.Receipts
public import EthLib.Execution.Proofs.Network.Status
public import EthLib.Execution.Proofs.Network.Transactions

/-!
# Proofs: the messages of the eth capability

Each message reads back from its ID and its RLP item, on every version that uses its form.

eth/68 rejects BlockRangeUpdate, and every version rejects an announcement whose lists differ in
length.

A response answers a request only when it repeats the request ID.

A BlockHeaders or a PooledTransactions that passes the check of its request answers it.
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
  GET_RECEIPTS_ID RECEIPTS_ID BLOCK_RANGE_UPDATE_ID

/-- The envelope `[request-id, payload]` reads back as its request ID and its payload. -/
theorem readEnvelope_envelope {α : Type} [Codec α] [LawfulCodec α] (i : UInt64) (x : α) :
    readEnvelope (envelope i (Codec.toItem x)) = .ok (i, x) := by
  simp [readEnvelope, envelope, Item.fields, Item.toItems, Item.field_toItem, bind, Except.bind,
    pure, Except.pure]

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

/-- The envelope of a version reads back as its request ID, its part and its payload, when the
part is present exactly from eth/70 on. -/
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

/-- A message has the form of a version.

Status and announcements have the form of their version, and an announcement has as many
types and sizes as hashes.

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

end Message

/-- Two errors with one code come from one constructor. -/
theorem EthError.code_injective (e₁ e₂ : EthError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [EthError.code] at h; exact absurd h (by decide))

end EthLib.Execution.Network
