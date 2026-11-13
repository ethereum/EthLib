module

public import EthLib.Cryptography.Hash.Tls13
public import EthLib.Cryptography.Proofs.Hash.Hkdf
public import EthLib.Base.Except
-- Checking a fixed label's byte length reduces the body of String.toUTF8.
import all Init.Data.String.Defs

/-!
# Proofs: TLS 1.3 labelled HKDF

Label serialization accepts exactly the field bounds of RFC 8446 §7.1.

The expansion adds only the output limit of HKDF-SHA-256, RFC 5869 §2.3.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Tls13

open EthLib.Base

/-- The typed extraction is HKDF-Extract of RFC 5869 §2.2, byte for byte. -/
theorem packBytes_extract (salt ikm : ByteArray) :
    packBytes (extract salt ikm) = Hkdf.extract salt ikm := rfl

/-- Label serialization accepts exactly the bounds of its three length fields. -/
theorem hkdfLabel_ok_iff (label context : ByteArray) (length : Nat) :
    (∃ info, hkdfLabel label context length = .ok info) ↔
      0 < label.size ∧ label.size ≤ 249 ∧ context.size ≤ 255 ∧ length ≤ 65535 := by
  by_cases hl : label.size = 0 ∨ 249 < label.size
  · simp only [hkdfLabel, hl, ↓reduceIte]
    simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
    omega
  · by_cases hc : 255 < context.size
    · simp only [hkdfLabel, hl, hc, ↓reduceIte]
      simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
      omega
    · by_cases hn : 65535 < length
      · simp only [hkdfLabel, hl, hc, hn, ↓reduceIte]
        simp [throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map]
        omega
      · simp only [hkdfLabel, hl, hc, hn, ↓reduceIte]
        simp [pure, Except.pure]
        omega

/-- A successful label writes its two-byte output length, length-prefixed label and context. -/
theorem hkdfLabel_eq (label context : ByteArray) (length : Nat)
    (hlabel : 0 < label.size ∧ label.size ≤ 249) (hcontext : context.size ≤ 255)
    (hlength : length ≤ 65535) :
    hkdfLabel label context length =
      .ok (⟨(natToBytes 2 length).toArray⟩ ++
        ⟨#[UInt8.ofNat (6 + label.size)]⟩ ++ "tls13 ".toUTF8 ++ label ++
        ⟨#[UInt8.ofNat context.size]⟩ ++ context) := by
  simp only [hkdfLabel, show ¬ (label.size = 0 ∨ 249 < label.size) by omega,
    show ¬ 255 < context.size by omega, show ¬ 65535 < length by omega, ↓reduceIte]
  simp only [ByteArray.size_append, show "tls13 ".toUTF8.size = 6 from by decide,
    ByteArray.append_assoc, pure, Except.pure]

/-- A labelled expansion succeeds exactly within the label, context and SHA-256 output bounds. -/
theorem expandLabel_ok_iff (secret : Secret) (label context : ByteArray) (length : Nat) :
    (∃ output, expandLabel secret label context length = .ok output) ↔
      0 < label.size ∧ label.size ≤ 249 ∧ context.size ≤ 255 ∧ length ≤ 8160 := by
  have hsecret : Hkdf.HASH_LEN ≤ (packBytes secret).size := by
    change 32 ≤ secret.toArray.size
    rw [secret.size_toArray]
    exact Nat.le_refl _
  have hlabel := hkdfLabel_ok_iff label context length
  unfold expandLabel
  cases hi : hkdfLabel label context length with
  | error e =>
    simp only [bind, Except.bind]
    constructor
    · rintro ⟨out, h⟩
      cases h
    · intro h
      obtain ⟨out, hout⟩ := hlabel.mpr ⟨h.1, h.2.1, h.2.2.1, by omega⟩
      rw [hi] at hout
      cases hout
  | ok info =>
    have hb := hlabel.mp ⟨info, hi⟩
    simp only [bind, Except.bind]
    split
    next e he =>
      simp only [throw, throwThe, MonadExceptOf.throw]
      constructor
      · rintro ⟨out, h⟩
        cases h
      · intro h
        obtain ⟨out, hout⟩ := Hkdf.expand_ok_iff.mpr ⟨hsecret, h.2.2.2⟩
        rw [he] at hout
        cases hout
    next out he =>
      have hl := (Hkdf.expand_ok_iff.mp ⟨out, he⟩).2
      simp only [Hkdf.HASH_LEN] at hl
      simp only [pure, Except.pure, Except.ok.injEq, exists_eq', true_iff]
      exact ⟨hb.1, hb.2.1, hb.2.2.1, hl⟩

/-- Every well-sized request returns an output of its stated length. -/
theorem expandLabel_ok (secret : Secret) (label context : ByteArray) (length : Nat)
    (hlabel : 0 < label.size ∧ label.size ≤ 249) (hcontext : context.size ≤ 255)
    (hlength : length ≤ 8160) :
    ∃ output, expandLabel secret label context length = .ok output :=
  (expandLabel_ok_iff secret label context length).mpr
    ⟨hlabel.1, hlabel.2, hcontext, hlength⟩

/-- A successful labelled expansion is HKDF with the serialized label as its `info` field. -/
theorem expandLabel_spec {secret : Secret} {label context : ByteArray} {length : Nat}
    {output : Vector UInt8 length} (h : expandLabel secret label context length = .ok output) :
    ∃ info, hkdfLabel label context length = .ok info ∧
      Hkdf.expand (packBytes secret) info length = .ok (packBytes output) := by
  unfold expandLabel at h
  cases hi : hkdfLabel label context length with
  | error e => simp [hi, bind, Except.bind] at h
  | ok info =>
    simp only [hi, bind, Except.bind] at h
    split at h
    next e he => simp [throw, throwThe, MonadExceptOf.throw] at h
    next out he =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst output
      exact ⟨info, rfl, he⟩

end EthLib.Cryptography.Hash.Tls13
