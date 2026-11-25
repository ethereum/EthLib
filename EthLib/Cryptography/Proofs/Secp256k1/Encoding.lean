module

public import EthLib.Base.Proofs.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Cryptography.Secp256k1.Encoding
public import EthLib.Cryptography.Proofs.Sec1
public import EthLib.Cryptography.Proofs.Secp256k1.Sqrt
public import EthLib.Cryptography.Proofs.Secp256k1.Order

/-!
# Proofs: the point encodings of secp256k1

The decoder accepts exactly the two encodings of the points other than `O`.

It returns the point that was encoded.

So the encodings are canonical: no other bytes decode to a point.

Each fact follows from the one for every curve, with the law of the square root of `Fp`.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

/-- The square root of `Fp` returns a root of each square, and `none` for each non-square. -/
theorem isSqrt_sqrt : Sec1.IsSqrt Fp.sqrt :=
  ⟨fun h => Fp.toZMod.injective (by rw [map_mul]; exact Fp.sqrt_mul_self h),
    fun h β hβ => Fp.sqrt_eq_none_iff.mp h (Fp.toZMod β) (by rw [← map_mul, hβ])⟩

/-- `y` and `-y` have opposite parities, unless `y = 0`. -/
theorem Fp.val_neg_mod_two {y : Fp} (hy : y ≠ 0) : (-y).val % 2 ≠ y.val % 2 :=
  EthLib.Cryptography.Secp256k1.val_neg_mod_two (y := Fp.toZMod y) (fun h => hy (Fp.toZMod.injective (h.trans Fp.toZMod_zero.symm)))

/-- Decompression gives the point of the curve with coordinate `x` and the given parity, if any. -/
theorem decompress_eq_ok_iff {x : Fp} {odd : Bool} {p : Point} :
    Point.decompress x odd = .ok p ↔
      ∃ y : Fp, p = .affine x y ∧ (Point.affine x y).isOnCurve = true ∧ decide (y.val % 2 = 1) = odd := by
  rw [Point.decompress, Base.mapError_ok_iff]
  exact Sec1.decompress_eq_ok_iff isSqrt_sqrt

namespace Point

/-- Validation keeps a point of the curve other than `O`, since the cofactor is 1. -/
private theorem validatePublicKey_eq_ok {p : Point} (hp : p.isOnCurve = true)
    (hinf : p ≠ infinity) : Sec1.validatePublicKey Fn.modulus 1 p = .ok p :=
  Sec1.validatePublicKey_eq_ok_iff.mpr ⟨rfl, hinf, hp, Or.inl rfl⟩

theorem decode_encodeCompressed {p : Point} (hp : p.isOnCurve = true) (hinf : p ≠ infinity) :
    decode p.encodeCompressed = .ok p := by
  rw [decode, Sec1.decode_encode isSqrt_sqrt true hp, Base.ok_bind,
    validatePublicKey_eq_ok hp hinf]
  rfl

theorem decode_encodeUncompressed {p : Point} (hp : p.isOnCurve = true) (hinf : p ≠ infinity) :
    decode p.encodeUncompressed = .ok p := by
  rw [decode, Sec1.decode_encode isSqrt_sqrt false hp, Base.ok_bind,
    validatePublicKey_eq_ok hp hinf]
  rfl

/-- The decoder accepts exactly the encodings of the points other than `O`.

It rejects a coordinate of `p` or more, an unknown prefix, and a pair off the curve.

It also rejects an `x` with no point, and `O`. -/
theorem decode_eq_ok_iff (bytes : ByteArray) (p : Point) :
    decode bytes = .ok p ↔
      p.isOnCurve = true ∧ p ≠ infinity ∧ (bytes = p.encodeCompressed ∨ bytes = p.encodeUncompressed) := by
  constructor
  · intro h
    rw [decode, Base.mapError_ok_iff] at h
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

/-- `O`, encoded as the single byte `00`, is not a public key. -/
theorem decode_infinity : decode infinity.encodeCompressed = .error .pointAtInfinity := by
  rw [decode, Sec1.decode_encode isSqrt_sqrt true rfl, Base.ok_bind]
  rfl

/-- An uncompressed pair off the curve is rejected. -/
theorem decode_notOnCurve {x y : Fp} (h : (affine x y).isOnCurve = false) :
    decode (affine x y).encodeUncompressed = .error .notOnCurve := by
  rw [decode, Sec1.decode_encode_false_of_isOnCurve_eq_false h]
  rfl

end Point

end EthLib.Cryptography.Secp256k1
