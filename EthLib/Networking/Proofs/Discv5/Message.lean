module

public import EthLib.Networking.Discv5.Message
public import EthLib.Networking.Discv5.Packet
public import EthLib.Serialization.Proofs.Rlp.Codec
public import EthLib.Serialization.Proofs.Rlp.RoundTrip

/-!
# `Networking.Proofs.Discv5.Message`

Properties of the discv5 messages.

- The fields of each message read back as the message.
- A valid message decodes back from its plaintext.
- A message that decodes is valid.
- A plaintext that decodes is the encoding of its message.
- So a message has at most one plaintext that decodes to it.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Discv5.Message

open EthLib.Networking.Discv5
open EthLib.Serialization.Rlp

/-- A port reads back from its item. -/
theorem portOfItem_portItem (port : UInt16) : portOfItem (portItem port) = .ok port := by
  simp [portOfItem, portItem, Item.toScalarBelow_scalar port.toNat_lt, bind, Except.bind, pure,
    Except.pure]

/-- The fields of each message read back as the message, under its type. -/
theorem ofFields_fields (m : Message) : Message.ofFields m.type m.fields = .ok (some m) := by
  cases m <;>
    simp [Message.ofFields, Message.fields, Message.type, LawfulCodec.ofItem_toItem,
      portOfItem_portItem, bind, Except.bind, pure, Except.pure]

/-- The type of every message is 1 to 10. -/
theorem type_range (m : Message) : 1 ≤ m.type.toNat ∧ m.type.toNat ≤ 10 := by
  cases m <;> simp [Message.type]

/-- A valid message decodes back from its plaintext. -/
theorem decode_encode {m : Message} {bytes : ByteArray} (h : m.encode = .ok bytes)
    (hv : m.valid = true) : Message.decode bytes = .ok m := by
  unfold Message.encode at h
  cases he : Serialization.Rlp.encode (.list m.fields) with
  | error e => simp [he, bind, Except.bind] at h
  | ok body =>
    simp only [he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hdec := Serialization.Rlp.decode_encode _ _ he
    have hrange := type_range m
    have hfields : Message.decodeFields (⟨#[m.type]⟩ ++ body) = .ok m := by
      simp [Message.decodeFields, hrange, Array.toArray_toList, hdec, Item.toItems,
        ofFields_fields, Except.mapError, bind, Except.bind, pure, Except.pure]
    simp [Message.decode, hfields, hv, bind, Except.bind, pure, Except.pure]

/-- A message that decodes passes the checks on its sizes and distances. -/
theorem valid_of_decode {bytes : ByteArray} {m : Message} (h : Message.decode bytes = .ok m) :
    m.valid = true := by
  unfold Message.decode at h
  cases hf : Message.decodeFields bytes with
  | error e => simp [hf, bind, Except.bind] at h
  | ok m' =>
    by_cases hv : m'.valid = true
    · simp [hf, hv, bind, Except.bind, pure, Except.pure] at h
      exact h ▸ hv
    · simp [hf, hv, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

/-! ## Canonical plaintexts -/

/-- An item reads as a port exactly when it is the item of that port. -/
theorem portOfItem_eq_ok_iff {item : Item} {port : UInt16} :
    portOfItem item = .ok port ↔ portItem port = item := by
  constructor
  · intro h
    simp only [portOfItem, Base.bind_ok_iff, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨n, hn, rfl⟩ := h
    obtain ⟨rfl, hlt⟩ := Item.eq_scalar_of_toScalarBelow hn
    simp [portItem, Nat.mod_eq_of_lt hlt]
  · rintro rfl
    exact portOfItem_portItem port

/-- Fields that read as a message are the fields of that message, under its type. -/
theorem fields_of_ofFields {type : UInt8} {items : List Item} {m : Message}
    (h : Message.ofFields type items = .ok (some m)) : m.type = type ∧ m.fields = items := by
  unfold Message.ofFields at h
  split at h
  all_goals
    simp only [Base.bind_ok_iff, Codec.ofItem_eq_ok_iff, portOfItem_eq_ok_iff, pure, Except.pure,
      Except.ok.injEq, Option.some.injEq, reduceCtorEq] at h
  -- Each field read is the item of what it read, and the last step substitutes the message.
  all_goals
    repeat obtain ⟨_, rfl, h⟩ := h
    exact ⟨UInt8.toNat_inj.mp (by simp_all [Message.type]), rfl⟩

/-- A plaintext that decodes, before the checks, is the encoding of its message. -/
theorem encode_of_decodeFields {bytes : ByteArray} {m : Message}
    (h : Message.decodeFields bytes = .ok m) : m.encode = .ok bytes := by
  unfold Message.decodeFields at h
  split at h
  · rename_i type rest hbytes
    split at h
    case isFalse => cases h
    -- Each step of the decoder succeeded, and each one is inverted by a step of the encoder.
    cases hd : Serialization.Rlp.decode ⟨rest.toArray⟩ with
    | error e => simp [hd, Except.mapError, bind, Except.bind] at h
    | ok item =>
      cases hi : item.toItems with
      | error e => simp [hd, hi, Except.mapError, bind, Except.bind] at h
      | ok items =>
        cases ho : Message.ofFields type items with
        | error e => simp [hd, hi, ho, Except.mapError, bind, Except.bind] at h
        | ok o =>
          cases o with
          | none => simp [hd, hi, ho, Except.mapError, bind, Except.bind] at h
          | some m' =>
            simp [hd, hi, ho, Except.mapError, bind, Except.bind, pure, Except.pure] at h
            obtain ⟨-, rfl⟩ := h
            obtain ⟨htype, hfields⟩ := fields_of_ofFields ho
            rw [Item.toItems_eq_ok] at hi
            subst hi
            have he := Serialization.Rlp.encode_decode _ _ hd
            simp only [Message.encode, hfields, he, htype, bind, Except.bind, pure, Except.pure,
              Except.ok.injEq]
            apply ByteArray.ext
            apply Array.toList_inj.mp
            simp [ByteArray.data_append, hbytes]
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A plaintext that decodes is the encoding of its message. -/
theorem encode_of_decode {bytes : ByteArray} {m : Message} (h : Message.decode bytes = .ok m) :
    m.encode = .ok bytes := by
  unfold Message.decode at h
  cases hf : Message.decodeFields bytes with
  | error e => simp [hf, bind, Except.bind] at h
  | ok m' =>
    by_cases hv : m'.valid = true
    · simp [hf, hv, bind, Except.bind, pure, Except.pure] at h
      exact h ▸ encode_of_decodeFields hf
    · simp [hf, hv, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

/-- A plaintext decodes to a message exactly when the message is valid and encodes to it. -/
theorem decode_eq_ok_iff (bytes : ByteArray) (m : Message) :
    Message.decode bytes = .ok m ↔ m.valid = true ∧ m.encode = .ok bytes :=
  ⟨fun h => ⟨valid_of_decode h, encode_of_decode h⟩, fun ⟨hv, he⟩ => decode_encode he hv⟩

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Networking.Discv5.MessageError.code_injective
    (e₁ e₂ : MessageError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [MessageError.code] at h; exact absurd h (by decide))

/-- A message error never has the code of a packet error, so one Python class carries both. -/
theorem _root_.EthLib.Networking.Discv5.MessageError.code_ne_packet
    (e : MessageError) (p : PacketError) : e.code ≠ p.code := by
  cases e <;> cases p <;> simp only [MessageError.code, PacketError.code] <;> decide

end EthLib.Networking.Proofs.Discv5.Message
