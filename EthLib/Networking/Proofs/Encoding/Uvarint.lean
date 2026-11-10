module

public import EthLib.Networking.Encoding.Uvarint
public import EthLib.Networking.Proofs.Encoding.Varint

/-!
# Proofs: multiformats unsigned varints

- A value below `2^63` encodes in at most nine bytes.
- Decoding reads back such a value from an encoding, whatever bytes follow it.
- The decoder accepts only these encodings, so each value has exactly one.
- Two errors with one code come from one constructor.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Encoding.Uvarint

open EthLib.Networking.Encoding.Uvarint
open EthLib.Networking.Encoding.Varint (groupSize payloadBits encodeAux)

/-- The bound is below `2^64`, so a value below it survives the conversion to 64 bits. -/
private theorem toNat_ofNat {n : Nat} (h : n < bound) : (UInt64.ofNat n).toNat = n := by
  rw [UInt64.toNat_ofNat_of_lt']
  simp only [bound] at h
  simp only [UInt64.size]
  omega

/-- A value below `2^63` encodes in at most nine bytes. -/
theorem encode_length_le {n : Nat} (h : n < bound) : (encode n).length ≤ maxLength := by
  have hn : n < groupSize ^ (8 + 1) := by
    simpa [bound, groupSize, payloadBits] using h
  have hv := toNat_ofNat h
  show (encodeAux (UInt64.ofNat n).toNat _).length ≤ maxLength
  rw [hv]
  exact Varint.length_encodeAux_le_of_lt (k := 8) hn

/-- Decoding an encoding followed by any bytes returns the value and those bytes. -/
theorem decode_encode {n : Nat} (h : n < bound) (rest : List UInt8) :
    decode (encode n ++ rest) = .ok (n, rest) := by
  have hv := toNat_ofNat h
  have hb : ¬ bound ≤ n := Nat.not_le.mpr h
  simp [decode, encode, Varint.split_encode, Varint.decode_encode, Except.mapError, bind,
    Except.bind, pure, Except.pure, hv, hb]

/-- A decoded value is below `2^63`, and the input is its encoding followed by the rest. -/
theorem encode_decode {bytes rest : List UInt8} {n : Nat} (h : decode bytes = .ok (n, rest)) :
    n < bound ∧ encode n ++ rest = bytes := by
  simp only [decode] at h
  cases hd : EthLib.Networking.Encoding.Varint.decode
      (EthLib.Networking.Encoding.Varint.split bytes).1 with
  | error e => simp [hd, Except.mapError, bind, Except.bind] at h
  | ok v =>
      simp only [hd, Except.mapError, bind, Except.bind] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hv := Varint.encode_decode hd
        refine ⟨by omega, ?_⟩
        have : UInt64.ofNat v.toNat = v := UInt64.ofNat_toNat
        rw [encode, this, hv]
        exact Varint.split_append bytes

/-- The decoder accepts exactly the encodings of values below `2^63`, then any bytes. -/
theorem decode_eq_ok_iff {bytes rest : List UInt8} {n : Nat} :
    decode bytes = .ok (n, rest) ↔ n < bound ∧ encode n ++ rest = bytes :=
  ⟨encode_decode, fun ⟨hn, he⟩ => he ▸ decode_encode hn rest⟩

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Networking.Encoding.Uvarint.UvarintError.code_injective
    (e₁ e₂ : UvarintError) (h : e₁.code = e₂.code) : e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [UvarintError.code] at h; exact absurd h (by decide))

end EthLib.Networking.Proofs.Encoding.Uvarint
