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
