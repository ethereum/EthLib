module

public import EthLib.Base.Proofs.Except
public import EthLib.Cryptography.Secp256r1.Encoding
public import EthLib.Cryptography.Proofs.Sec1
public import EthLib.Cryptography.Proofs.Secp256r1.Field

/-!
# Proofs: the point encodings of secp256r1

The decoder accepts exactly the two encodings of the points other than `O`.

It returns the point that was encoded, so no other bytes decode to a point.

The uncompressed decoder accepts exactly the uncompressed encodings.

Each fact follows from the one for every curve, with the square root for `p = 3 mod 4`.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256r1

/-- The square root of `Fp` returns a root of each square, and `none` for each non-square. -/
theorem isSqrt_sqrt : Sec1.IsSqrt sec1.sqrt? := by
  -- Reducing the projection first keeps unification off the field's arithmetic.
  simp only [sec1]
  exact Sec1.isSqrt_sqrt3Mod4 (by decide)

namespace Point

theorem decode_encodeCompressed {p : Point} (hp : p.isOnCurve = true) (hinf : p ≠ infinity) :
    decode p.encodeCompressed = .ok p := by
  rw [decode, Sec1.decode_encode isSqrt_sqrt true hp, Base.ok_bind,
    Sec1.validatePublicKey_one_eq_ok hp hinf]

theorem decode_encodeUncompressed {p : Point} (hp : p.isOnCurve = true) (hinf : p ≠ infinity) :
    decode p.encodeUncompressed = .ok p := by
  rw [decode, Sec1.decode_encode isSqrt_sqrt false hp, Base.ok_bind,
    Sec1.validatePublicKey_one_eq_ok hp hinf]

/-- The decoder accepts exactly the encodings of the points other than `O`. -/
theorem decode_eq_ok_iff {bytes : ByteArray} {p : Point} :
    decode bytes = .ok p ↔
      p.isOnCurve = true ∧ p ≠ infinity ∧
        (bytes = p.encodeCompressed ∨ bytes = p.encodeUncompressed) := by
  constructor
  · intro h
    rw [decode] at h
    cases hd : Sec1.decode sec1 bytes with
    | error e => rw [hd] at h; cases h
    | ok q =>
      rw [hd, Base.ok_bind, Sec1.validatePublicKey_eq_ok_iff] at h
      obtain ⟨rfl, hinf, hon, -⟩ := h
      obtain ⟨-, c, hc⟩ := (Sec1.decode_eq_ok_iff isSqrt_sqrt).mp hd
      refine ⟨hon, hinf, ?_⟩
      cases c
      · exact Or.inr hc
      · exact Or.inl hc
  · rintro ⟨hon, hinf, rfl | rfl⟩
    · exact decode_encodeCompressed hon hinf
    · exact decode_encodeUncompressed hon hinf

theorem size_encodeCompressed (x y : Fp) : (affine x y).encodeCompressed.size = 33 :=
  Sec1.size_encode_true sec1 x y

theorem size_encodeUncompressed (x y : Fp) : (affine x y).encodeUncompressed.size = 65 :=
  Sec1.size_encode_false sec1 x y

/-- The uncompressed decoder accepts exactly the uncompressed encodings of points on the curve.

It returns the point `(x, y)` of each. -/
theorem decodeUncompressed_eq_some_iff {bytes : ByteArray} {point : Point} :
    decodeUncompressed bytes = some point ↔
      ∃ x y : Fp, point = .affine x y ∧ point.isOnCurve = true ∧
        bytes = (affine x y).encodeUncompressed := by
  rw [decodeUncompressed]
  constructor
  · intro h
    split at h
    · rename_i hs
      obtain ⟨hon, hinf, hb⟩ := decode_eq_ok_iff.mp (Base.toOption_eq_some_iff.mp h)
      cases point with
      | infinity => exact absurd rfl hinf
      | affine x y =>
        refine ⟨x, y, rfl, hon, ?_⟩
        rcases hb with rfl | rfl
        · rw [size_encodeCompressed] at hs
          cases hs
        · rfl
    · cases h
  · rintro ⟨x, y, rfl, hon, rfl⟩
    simp only [size_encodeUncompressed, ↓reduceIte, Base.toOption_eq_some_iff]
    exact decode_encodeUncompressed hon (by simp)

end Point

end EthLib.Cryptography.Secp256r1
