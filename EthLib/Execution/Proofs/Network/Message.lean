module

public import EthLib.Execution.Network.Message
public import EthLib.Execution.Proofs.Network.Blocks
public import EthLib.Execution.Proofs.Network.Status

/-!
# Proofs: the messages of the eth capability

Each message reads back from its ID and its RLP item, on every version that uses its form.

eth/68 rejects BlockRangeUpdate.

A response answers a request only when it repeats the request ID, and a BlockHeaders that passes
the check of its GetBlockHeaders answers it.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Serialization.Rlp

namespace Message

-- The message IDs are numbers, so each case of the decoder is decided by their values.
attribute [local simp] STATUS_ID NEW_BLOCK_HASHES_ID GET_BLOCK_HEADERS_ID BLOCK_HEADERS_ID
  GET_BLOCK_BODIES_ID BLOCK_BODIES_ID NEW_BLOCK_ID BLOCK_RANGE_UPDATE_ID

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

/-- A message has the form of a version.

Status has the form of its version, BlockRangeUpdate exists from eth/69 on, and the other
messages have one form at every version. -/
def FitsVersion (version : EthVersion) : Message → Prop
  | .status (.eth68 ..) => version = .eth68
  | .status (.eth69 ..) => version ≠ .eth68
  | .blockRangeUpdate _ => EthVersion.eth69 ≤ version
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
    simp [ofItem, Message.id, toItem, hm, BLOCK_RANGE_UPDATE_ID,
      LawfulCodec.ofItem_toItem, Functor.map, Except.map, Except.mapError]
  | newBlockHashes bs =>
    simp [ofItem, Message.id, toItem, LawfulCodec.ofItem_toItem,
      Functor.map, Except.map, Except.mapError]
  | getBlockHeaders i r =>
    simp [ofItem, Message.id, toItem, GET_BLOCK_HEADERS_ID,
      readEnvelope_envelope, Functor.map, Except.map, Except.mapError]
  | blockHeaders i hs =>
    simp [ofItem, Message.id, toItem, GET_BLOCK_HEADERS_ID,
      list_eq_toItem hs, readEnvelope_envelope, Functor.map, Except.map,
      Except.mapError]
  | getBlockBodies i hs =>
    simp [ofItem, Message.id, toItem, GET_BLOCK_HEADERS_ID,
      readEnvelope_envelope, Functor.map, Except.map,
      Except.mapError]
  | blockBodies i bs =>
    simp [ofItem, Message.id, toItem, GET_BLOCK_HEADERS_ID,
      list_eq_toItem bs,
      readEnvelope_envelope, Functor.map, Except.map, Except.mapError]
  | newBlock b td =>
    simp [ofItem, Message.id, toItem, GET_BLOCK_HEADERS_ID,
      Item.fields,
      Item.toItems, Item.field_toItem, bind, Except.bind, pure, Except.pure, Except.mapError]

/-- eth/68 rejects BlockRangeUpdate, which eth/69 adds. -/
theorem ofItem_blockRangeUpdate_eth68 (item : Item) :
    ofItem .eth68 BLOCK_RANGE_UPDATE_ID item = .error (.unknownId BLOCK_RANGE_UPDATE_ID) := by
  have : ¬ EthVersion.eth69 ≤ .eth68 := by decide
  simp [ofItem, BLOCK_HEADERS_ID,
    this]

/-- A response that answers a request is a response with the request ID of the request. -/
theorem requestId_of_answers {request response : Message} (h : answers request response) :
    ∃ i, request.requestId? = some i ∧ response.requestId? = some i := by
  cases request <;> cases response <;> simp_all [answers, requestId?]

/-- Every response type answers its request type when it repeats the request ID. -/
theorem answers_of_requestId (i : UInt64) (r : HeaderRequest) (hs : List Item)
    (hashes : List Hash32) (bs : List Item) :
    answers (getBlockHeaders i r) (blockHeaders i hs) ∧
      answers (getBlockBodies i hashes) (blockBodies i bs) := by
  simp [answers]

/-- A response that passes the check answers the request, with its request ID. -/
theorem answers_of_checkHeaderResponse {request response : Message}
    (h : checkHeaderResponse request response = .ok ()) : answers request response := by
  unfold checkHeaderResponse at h
  split at h
  · rename_i i r j hs
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
