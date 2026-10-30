import EthLib.Cryptography.Secp256k1.Encoding
import EthLib.Cryptography.Proofs.Secp256k1.Order
import EthLib.Cryptography.Proofs.Hash.Keccak256

/-!
# Proofs: the point encodings of secp256k1

The decoder accepts exactly the two encodings of the points other than `O`, and returns the point encoded.

- `decode_encodeCompressed`, `decode_encodeUncompressed`: decoding undoes either encoding.
- `decode_eq_ok_iff`: a decoded point is on the curve, is not `O`, and the input is one of its two encodings.

So the encodings are canonical: no other bytes decode to a point.

That rules out a coordinate of `p` or more, an unknown prefix, a pair off the curve, an `x` with no point, and `O`.
-/

namespace EthLib.Cryptography.Secp256k1

/-! ## Big-endian bytes -/

theorem length_toBytesBE (k v : Nat) : (toBytesBE k v).length = k := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => simp [toBytesBE, ih]

theorem ofBytesBE_append_singleton (l : List UInt8) (b : UInt8) :
    ofBytesBE (l ++ [b]) = 256 * ofBytesBE l + b.toNat := by
  simp [ofBytesBE, List.foldl_append]

/-- Reading the bytes of `v` gives `v mod 256^k`. -/
theorem ofBytesBE_toBytesBE (k v : Nat) : ofBytesBE (toBytesBE k v) = v % 256 ^ k := by
  induction k generalizing v with
  | zero => simp [toBytesBE, ofBytesBE, Nat.mod_one]
  | succ k ih =>
    have hb : (UInt8.ofNat (v % 256)).toNat = v % 256 := by
      rw [UInt8.toNat_ofNat']
      exact Nat.mod_mod_of_dvd _ (by decide)
    rw [toBytesBE, ofBytesBE_append_singleton, ih, hb, Nat.pow_succ', Nat.mod_mul]
    ring

/-- Bytes read as an integer and written back are unchanged. -/
theorem toBytesBE_ofBytesBE (l : List UInt8) : toBytesBE l.length (ofBytesBE l) = l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l b ih =>
    rw [List.length_append, List.length_singleton, toBytesBE, ofBytesBE_append_singleton]
    have hb := b.toNat_lt
    rw [show (256 * ofBytesBE l + b.toNat) / 256 = ofBytesBE l by omega,
      show (256 * ofBytesBE l + b.toNat) % 256 = b.toNat by omega, ih, UInt8.ofNat_toNat]

theorem ofBytesBE_lt (l : List UInt8) : ofBytesBE l < 256 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => decide
  | append_singleton l b ih =>
    rw [ofBytesBE_append_singleton, List.length_append, List.length_singleton, Nat.pow_succ]
    have := b.toNat_lt
    omega

theorem Fp.length_toBytes (x : Fp) : x.toBytes.length = 32 := length_toBytesBE 32 x.val

theorem Fp.ofBytes_toBytes (x : Fp) : Fp.ofBytes x.toBytes = .ok x := by
  have h : ofBytesBE x.toBytes = x.val := by
    rw [Fp.toBytes, ofBytesBE_toBytesBE, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]
  simp only [Fp.ofBytes, h, x.isLt, dite_true]

/-- 32 bytes that read as a coordinate are that coordinate's bytes. -/
theorem Fp.toBytes_of_ofBytes {l : List UInt8} {x : Fp} (hl : l.length = 32) (h : Fp.ofBytes l = .ok x) :
    x.toBytes = l := by
  simp only [Fp.ofBytes] at h
  split at h
  · cases h
    rw [Fp.toBytes, ← hl]
    exact toBytesBE_ofBytesBE l
  · cases h

/-! ## Decompression -/

/-- `y` and `-y` have opposite parities, unless `y = 0`. -/
theorem Fp.val_neg_mod_two {y : Fp} (hy : y ≠ 0) : (-y).val % 2 ≠ y.val % 2 :=
  EthLib.Cryptography.Secp256k1.val_neg_mod_two (y := Fp.toZMod y) (fun h => hy (Fp.toZMod.injective (h.trans Fp.toZMod_zero.symm)))

/-- Two points of the curve with the same `x` and the same parity of `y` are equal. -/
theorem Fp.eq_of_parity {x y1 y2 : Fp} (h1 : (Point.affine x y1).isOnCurve = true)
    (h2 : (Point.affine x y2).isOnCurve = true) (hpar : y1.val % 2 = y2.val % 2) : y1 = y2 :=
  Fp.toZMod.injective (y_eq_of_parity ((Point.isOnCurve_affine x y1).mp h1) ((Point.isOnCurve_affine x y2).mp h2) hpar)

/-- The right-hand side of the equation, `x^3 + 7`, in `ZMod p`. -/
private theorem toZMod_rhs (x : Fp) : Fp.toZMod (x * x * x + b) = Fp.toZMod x * Fp.toZMod x * Fp.toZMod x + 7 := by
  rw [map_add, map_mul, map_mul]
  rfl

/-- A root of `x^3 + 7` gives a point of the curve. -/
private theorem isOnCurve_of_sqrt {x c : Fp} (h : (x * x * x + b).sqrt = some c) :
    (Point.affine x c).isOnCurve = true := by
  rw [Point.isOnCurve_affine, ← toZMod_rhs]
  exact Fp.sqrt_mul_self h

/-- A root of `x^3 + 7` is not `0`, since `-7` is not a cube. -/
private theorem sqrt_ne_zero {x c : Fp} (h : (x * x * x + b).sqrt = some c) : c ≠ 0 := by
  rintro rfl
  have h0 := (Point.isOnCurve_affine x 0).mp (isOnCurve_of_sqrt h)
  exact cube_ne_neg_seven (Fp.toZMod x) (by rw [Fp.toZMod_zero] at h0; linear_combination -h0)

/-- `decompress x odd` is the point of the curve with coordinate `x` and parity `odd`, when it exists. -/
theorem decompress_eq_ok_iff {x : Fp} {odd : Bool} {p : Point} :
    Point.decompress x odd = .ok p ↔
      ∃ y : Fp, p = .affine x y ∧ (Point.affine x y).isOnCurve = true ∧ decide (y.val % 2 = 1) = odd := by
  unfold Point.decompress
  cases hs : (x * x * x + b).sqrt with
  | none =>
    dsimp only
    refine ⟨fun h => (by cases h), ?_⟩
    rintro ⟨y, rfl, hc, -⟩
    -- `y` would be a root of `x^3 + 7`.
    refine absurd ((Fp.sqrt_eq_none_iff.mp hs) (Fp.toZMod y) ?_) (fun h => h)
    rw [toZMod_rhs]
    exact (Point.isOnCurve_affine x y).mp hc
  | some beta =>
    dsimp only
    have hon := isOnCurve_of_sqrt hs
    have hne := Fp.val_neg_mod_two (sqrt_ne_zero hs)
    have honneg : (Point.affine x (-beta)).isOnCurve = true := Point.isOnCurve_neg hon
    have h2 := Nat.mod_two_eq_zero_or_one beta.val
    have h2' := Nat.mod_two_eq_zero_or_one (-beta).val
    constructor
    · rintro ⟨⟩
      split
      · exact ⟨beta, rfl, hon, by assumption⟩
      · refine ⟨-beta, rfl, honneg, ?_⟩
        rename_i hpar
        cases odd <;> simp_all
    · rintro ⟨y, rfl, hc, hpar⟩
      -- The parity picks the root `y` among `beta` and `-beta`.
      have hy : (if decide (beta.val % 2 = 1) = odd then beta else -beta) = y := by
        split
        · rename_i hb
          exact Fp.eq_of_parity hon hc (by cases odd <;> simp_all)
        · rename_i hb
          exact Fp.eq_of_parity honneg hc (by cases odd <;> simp_all)
      rw [hy]

namespace Point

/-! ## Round trips -/

/-- A byte array is the array of its bytes. -/
private theorem byteArray_eq {bytes : ByteArray} {l : List UInt8} (h : bytes.data.toList = l) :
    bytes = ⟨l.toArray⟩ := by
  subst h
  rfl

/-- The prefix of the compressed form is `03` exactly when `y` is odd. -/
private theorem prefix_eq_three (y : Fp) :
    ((if y.val % 2 = 0 then (0x02 : UInt8) else 0x03) == 0x03) = decide (y.val % 2 = 1) := by
  rcases Nat.mod_two_eq_zero_or_one y.val with h | h <;> simp [h]

theorem decode_encodeCompressed {p : Point} (hp : p.isOnCurve = true) (hinf : p ≠ infinity) :
    decode p.encodeCompressed = .ok p := by
  cases p with
  | infinity => exact absurd rfl hinf
  | affine x y =>
    have hd : decompress x (decide (y.val % 2 = 1)) = .ok (affine x y) := decompress_eq_ok_iff.mpr ⟨y, rfl, hp, rfl⟩
    have htag : (if y.val % 2 = 0 then (0x02 : UInt8) else 0x03) = 0x02
        ∨ (if y.val % 2 = 0 then (0x02 : UInt8) else 0x03) = 0x03 := by
      split <;> simp
    have hne : ¬((if y.val % 2 = 0 then (0x02 : UInt8) else 0x03) = 0x00 ∧ x.toBytes = []) := by
      rintro ⟨-, h⟩
      have := Fp.length_toBytes x
      rw [h] at this
      cases this
    simp only [decode, encodeCompressed, List.toList_toArray, Fp.length_toBytes, ite_eq_right hne, ite_eq_left htag,
      Fp.ofBytes_toBytes, prefix_eq_three, hd, bind, Except.bind, ite_true]

theorem decode_encodeUncompressed {p : Point} (hp : p.isOnCurve = true) (hinf : p ≠ infinity) :
    decode p.encodeUncompressed = .ok p := by
  cases p with
  | infinity => exact absurd rfl hinf
  | affine x y =>
    have hlen : (x.toBytes ++ y.toBytes).length = 64 := by simp [Fp.length_toBytes]
    have hne : ¬((0x04 : UInt8) = 0x00 ∧ x.toBytes ++ y.toBytes = []) := by
      rintro ⟨h, -⟩
      cases h
    have htake : (x.toBytes ++ y.toBytes).take 32 = x.toBytes := by
      rw [List.take_append_of_le_length (by rw [Fp.length_toBytes]), List.take_of_length_le (by rw [Fp.length_toBytes])]
    have hdrop : (x.toBytes ++ y.toBytes).drop 32 = y.toBytes := by
      rw [List.drop_append_of_le_length (by rw [Fp.length_toBytes]), List.drop_of_length_le (by rw [Fp.length_toBytes]),
        List.nil_append]
    simp only [decode, encodeUncompressed, List.toList_toArray, List.cons_append, hlen, hne, htake, hdrop,
      Fp.ofBytes_toBytes, hp, bind, Except.bind, ite_true, ite_false, (by decide : ¬(64 : Nat) = 32)]

/-- The decoder accepts exactly the encodings of the points other than `O`. -/
theorem decode_eq_ok_iff (bytes : ByteArray) (p : Point) :
    decode bytes = .ok p ↔
      p.isOnCurve = true ∧ p ≠ infinity ∧ (bytes = p.encodeCompressed ∨ bytes = p.encodeUncompressed) := by
  constructor
  · intro h
    unfold decode at h
    cases hl : bytes.data.toList with
    | nil => rw [hl] at h; cases h
    | cons tag rest =>
      rw [hl] at h
      dsimp only at h
      split_ifs at h with h0 h32 htag h64 h4
      · -- Compressed: `x` read from the bytes, then the point with the parity of the prefix.
        cases hx : Fp.ofBytes rest with
        | error e => rw [hx] at h; cases h
        | ok x =>
          rw [hx] at h
          simp only [bind, Except.bind] at h
          obtain ⟨y, rfl, hc, hpar⟩ := decompress_eq_ok_iff.mp h
          refine ⟨hc, by simp, Or.inl ?_⟩
          -- The prefix is `02` for an even `y` and `03` for an odd one.
          have hprefix : (if y.val % 2 = 0 then (0x02 : UInt8) else 0x03) = tag := by
            rcases htag with rfl | rfl <;> rcases Nat.mod_two_eq_zero_or_one y.val with hy | hy <;>
              simp only [hy] at hpar ⊢ <;> simp at hpar ⊢
          rw [byteArray_eq hl, encodeCompressed, Fp.toBytes_of_ofBytes h32 hx, hprefix]
      · -- Uncompressed: both coordinates, on the curve.
        cases hx : Fp.ofBytes (rest.take 32) with
        | error e => rw [hx] at h; cases h
        | ok x =>
          cases hy : Fp.ofBytes (rest.drop 32) with
          | error e => rw [hx, hy] at h; cases h
          | ok y =>
            rw [hx, hy] at h
            dsimp only [bind, Except.bind] at h
            split at h
            · rename_i hc
              cases h
              refine ⟨hc, by simp, Or.inr ?_⟩
              rw [byteArray_eq hl, encodeUncompressed, h4,
                Fp.toBytes_of_ofBytes (by simp [h64]) hx, Fp.toBytes_of_ofBytes (by simp [h64]) hy,
                List.cons_append, List.take_append_drop]
            · cases h
  · rintro ⟨hp, hinf, h | h⟩ <;> subst h
    · exact decode_encodeCompressed hp hinf
    · exact decode_encodeUncompressed hp hinf

theorem size_encodeCompressed (x y : Fp) : (affine x y).encodeCompressed.size = 33 := by
  simp [encodeCompressed, ByteArray.size, Fp.length_toBytes]

theorem size_encodeUncompressed (x y : Fp) : (affine x y).encodeUncompressed.size = 65 := by
  simp [encodeUncompressed, ByteArray.size, Fp.length_toBytes]

/-- `O`, encoded as the single byte `00`, is not a public key. -/
theorem decode_infinity : decode infinity.encodeCompressed = .error .pointAtInfinity := rfl

/-- An uncompressed pair off the curve is rejected. -/
theorem decode_notOnCurve {x y : Fp} (h : (affine x y).isOnCurve = false) :
    decode ⟨(0x04 :: x.toBytes ++ y.toBytes).toArray⟩ = .error .notOnCurve := by
  have hlen : (x.toBytes ++ y.toBytes).length = 64 := by simp [Fp.length_toBytes]
  have htake : (x.toBytes ++ y.toBytes).take 32 = x.toBytes := by
    rw [List.take_append_of_le_length (by rw [Fp.length_toBytes]), List.take_of_length_le (by rw [Fp.length_toBytes])]
  have hdrop : (x.toBytes ++ y.toBytes).drop 32 = y.toBytes := by
    rw [List.drop_append_of_le_length (by rw [Fp.length_toBytes]), List.drop_of_length_le (by rw [Fp.length_toBytes]),
      List.nil_append]
  simp only [decode, List.cons_append, hlen, htake, hdrop, Fp.ofBytes_toBytes, h, bind,
    Except.bind, (by decide : ¬(64 : Nat) = 32), ite_true, ite_false, Bool.false_eq_true]
  rfl

/-! ## Known answers

The two encodings of `G` are printed in SEC 2 v2 §2.4.1.

Each claim is evaluated by the kernel, square root included. -/

open Hash.Keccak (hexBytes)

/-- The result of a decoding, as an option: equality of options is decidable. -/
private def decoded (r : Except Secp256k1Error Point) : Option Point := r.toOption

/-- The error of a decoding, or `none`. -/
private def decodeError (r : Except Secp256k1Error Point) : Option Secp256k1Error :=
  match r with
  | .error e => some e
  | .ok _ => none

/-- `G` compressed, as SEC 2 prints it. -/
theorem encodeCompressed_generator :
    generator.encodeCompressed.data = (hexBytes "0279BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798").data := by
  decide +kernel

/-- `G` uncompressed, as SEC 2 prints it. -/
theorem encodeUncompressed_generator :
    generator.encodeUncompressed.data = (hexBytes "0479BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8").data := by
  decide +kernel

/-- The compressed bytes of SEC 2 decode to `G`: the square root recovers its `y`. -/
theorem decode_generator_compressed : decoded (decode (hexBytes "0279BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798")) = some generator := by
  decide +kernel

/-- The uncompressed bytes of SEC 2 decode to `G`. -/
theorem decode_generator_uncompressed :
    decoded (decode (hexBytes "0479BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8")) = some generator := by
  decide +kernel

/-- `G` with `y + 1` is off the curve. -/
theorem decode_generator_y_plus_one :
    decodeError (decode (hexBytes "0479BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B9")) = some .notOnCurve := by
  decide +kernel

/-- `x = 2^256 - 1` is not below `p`. -/
theorem decode_x_too_large : decodeError (decode (hexBytes "02FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF")) = some .coordinateTooLarge := by
  decide +kernel

/-- `x = 0` has no point: `7` is not a square mod `p`. -/
theorem decode_x_zero : decodeError (decode (hexBytes "020000000000000000000000000000000000000000000000000000000000000000")) = some .noPointWithX := by
  decide +kernel

/-- `05` is no prefix. -/
theorem decode_prefix_05 : decodeError (decode (hexBytes "0579BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798")) = some (.invalidPrefix 0x05) := by
  decide +kernel

/-- The 64 coordinate bytes alone, without a prefix, have no valid length. -/
theorem decode_no_prefix : decodeError (decode (hexBytes "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8")) = some (.invalidEncodingLength 64) := by
  decide +kernel

end Point

end EthLib.Cryptography.Secp256k1
