module

public import EthLib.Networking.Libp2p.Multistream
public import EthLib.Networking.Proofs.Encoding.Uvarint

/-!
# Proofs: multistream-select messages

- Decoding reads back a message from its encoding, whatever bytes follow it.
- The decoder accepts only these encodings, so each message has exactly one.
- A peer echoes a proposal it supports, and answers `na` to any other.
- Two errors with one code come from one constructor.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Libp2p.Multistream

open EthLib.Networking.Encoding
open EthLib.Networking.Libp2p.Multistream

/-- Decoding the encoding of a message, then any bytes, returns the message and those bytes.

The message and its newline must be shorter than `2^63` bytes. -/
theorem decode_encode (message : ByteArray) (h : message.size + 1 < Uvarint.bound)
    (rest : List UInt8) : decode (encode message ++ rest) = .ok (message, rest) := by
  obtain ⟨⟨bs⟩⟩ := message
  have hlen : (ByteArray.mk ⟨bs⟩).size = bs.length := by simp [ByteArray.size]
  have hass : encode ⟨⟨bs⟩⟩ ++ rest =
      Uvarint.encode (bs.length + 1) ++ (bs ++ newline :: rest) := by
    simp [encode, hlen]
  rw [hass]
  rw [hlen] at h
  simp only [decode]
  rw [EthLib.Networking.Proofs.Encoding.Uvarint.decode_encode h]
  have h1 : (bs ++ newline :: rest).take (bs.length + 1) = bs ++ [newline] := by
    rw [List.take_append, List.take_of_length_le (by omega)]
    simp
  have h2 : (bs ++ newline :: rest).drop (bs.length + 1) = rest := by
    rw [List.drop_append]
    simp
  simp [h1, h2, bind, Except.bind, Except.mapError]
  rfl

/-- A decoded message and its newline are shorter than `2^63` bytes.

The input is the encoding of that message, then the rest. -/
theorem encode_decode {bytes rest : List UInt8} {message : ByteArray}
    (h : decode bytes = .ok (message, rest)) :
    message.size + 1 < Uvarint.bound ∧ encode message ++ rest = bytes := by
  simp only [decode] at h
  cases hd : Uvarint.decode bytes with
  | error e => simp [hd, bind, Except.bind, Except.mapError] at h
  | ok p =>
      obtain ⟨L, r0⟩ := p
      obtain ⟨hL, hb⟩ := EthLib.Networking.Proofs.Encoding.Uvarint.encode_decode hd
      simp only [hd, bind, Except.bind, Except.mapError] at h
      generalize hbody : r0.take L = body at h
      by_cases h0 : L = 0
      · simp [h0, throw, throwThe, MonadExceptOf.throw] at h
      by_cases h1 : body.length < L
      · simp [h0, h1, throw, throwThe, MonadExceptOf.throw] at h
      by_cases h2 : body[L - 1]? = some newline
      · simp only [h0, h1, h2, ne_eq, not_true_eq_false, ite_false] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hlen : body.length = L := by
          have : body.length ≤ L := by rw [← hbody]; simp; omega
          omega
        have hsz : (⟨(body.take (L - 1)).toArray⟩ : ByteArray).size = L - 1 := by
          simp [ByteArray.size]; omega
        have hi : L - 1 < body.length := by omega
        have hg : body[L - 1] = newline := by simpa [hi] using h2
        have hdrop : body.drop (L - 1) = [newline] := by
          rw [List.drop_eq_getElem_cons hi, hg, List.drop_of_length_le (by omega)]
        have hr0 : body.take (L - 1) ++ newline :: r0.drop L = r0 := by
          calc body.take (L - 1) ++ newline :: r0.drop L
              = body.take (L - 1) ++ body.drop (L - 1) ++ r0.drop L := by
                rw [hdrop]; simp
            _ = r0 := by rw [List.take_append_drop, ← hbody, List.take_append_drop]
        refine ⟨by omega, ?_⟩
        rw [← hb]
        have hL' : L - 1 + 1 = L := by omega
        simp only [encode, hsz, hL', List.append_assoc, List.singleton_append]
        rw [hr0]
      · simp [h0, h1, h2, throw, throwThe, MonadExceptOf.throw] at h

/-- The decoder accepts exactly the encodings of messages that fit, then any bytes. -/
theorem decode_eq_ok_iff {bytes rest : List UInt8} {message : ByteArray} :
    decode bytes = .ok (message, rest) ↔
      message.size + 1 < Uvarint.bound ∧ encode message ++ rest = bytes :=
  ⟨encode_decode, fun ⟨hn, he⟩ => he ▸ decode_encode message hn rest⟩

/-- A peer echoes a proposal it supports. -/
theorem respond_of_mem {supported : List ByteArray} {proposal : ByteArray}
    (h : proposal ∈ supported) : respond supported proposal = proposal := by
  simp only [respond, List.mem_map]
  exact ite_eq_left ⟨proposal, h, rfl⟩

/-- A peer answers `na` to a proposal it does not support. -/
theorem respond_of_not_mem {supported : List ByteArray} {proposal : ByteArray}
    (h : proposal ∉ supported) : respond supported proposal = notAvailable := by
  simp only [respond, List.mem_map]
  refine ite_eq_right ?_
  rintro ⟨p, hp, he⟩
  exact h (ByteArray.ext he ▸ hp)

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Networking.Libp2p.Multistream.MultistreamError.code_injective
    (e₁ e₂ : MultistreamError) (h : e₁.code = e₂.code) : e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [MultistreamError.code] at h; exact absurd h (by decide))

end EthLib.Networking.Proofs.Libp2p.Multistream
