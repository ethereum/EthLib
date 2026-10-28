import EthLib.Cryptography.Bls.Compress
import EthLib.Cryptography.Proofs.Bls.G1Group
import EthLib.Cryptography.Proofs.IdLoops
import EthLib.Cryptography.Proofs.Kzg.Polynomials

/-!
# Proofs: `Fp.sqrt` and the G1 compressed-encoding round-trip

`Fp.sqrt` computes `a^((p+1)/4)`, which squares back to `a` exactly on
quadratic residues (`p ≡ 3 (mod 4)`): soundness (`sqrt_ok`) is the
spec's own final check, completeness (`sqrt_complete`) is Euler's
criterion. On top of this, `uncompress_compress` shows that
decompressing a compressed valid point recovers the same group
element (the Jacobian representative changes — compression
normalizes to `z = 1` — but its `toPoint` does not).

The converse direction shows that the encoding is canonical.

- Every point that decompression returns lies on the curve.
- Compressing it gives back the exact input bytes.
- So two different byte strings never decode to the same point.
-/
deriving instance DecidableEq for EthLib.Cryptography.Bls.BlsError
deriving instance DecidableEq for EthLib.Cryptography.Bls.G1

namespace EthLib.Cryptography.Bls.Fp

set_option maxRecDepth 4000

/-- `Fp.beq` in `ZMod` form (compare `G1.beq_iff`). -/
private theorem beq_iff' {a b : Fp} :
    a.beq b = true ↔ (a : ZMod Fp.modulus) = b := by
  rw [Fp.beq, beq_iff_eq]
  exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩

/-- Soundness of `Fp.sqrt`: a returned root squares to the input. -/
theorem sqrt_ok {a c : Fp} (h : Fp.sqrt a = .ok c) :
    (c : ZMod Fp.modulus) * c = a := by
  rw [Fp.sqrt] at h
  split at h
  · rename_i hbeq
    cases h
    exact beq_iff'.mp hbeq
  · cases h

/-- The core Euler-criterion computation, phrased over `ZMod`. -/
private theorem pow_sqrt_exponent {x y : ZMod Fp.modulus} (h : y * y = x) :
    x ^ ((Fp.modulus + 1) / 4) * x ^ ((Fp.modulus + 1) / 4) = x := by
  by_cases hy : y = 0
  · subst hy
    rw [← h, mul_zero, zero_pow (by decide : (Fp.modulus + 1) / 4 ≠ 0),
        mul_zero]
  · subst h
    rw [← pow_add, ← pow_two, ← pow_mul,
        show 2 * ((Fp.modulus + 1) / 4 + (Fp.modulus + 1) / 4)
          = (Fp.modulus - 1) + 2 by decide,
        pow_add, ZMod.pow_card_sub_one_eq_one hy, one_mul, pow_two]

/-- Completeness of `Fp.sqrt`: it succeeds on every square. -/
theorem sqrt_complete {a b : Fp} (h : (b : ZMod Fp.modulus) * b = a) :
    Fp.sqrt a = .ok (Fp.powNat a ((Fp.modulus + 1) / 4)) := by
  have hcand : (Fp.powNat a ((Fp.modulus + 1) / 4) : ZMod Fp.modulus)
      * Fp.powNat a ((Fp.modulus + 1) / 4) = a := by
    rw [powNat_eq_zmod_pow a ((Fp.modulus + 1) / 4)]
    exact pow_sqrt_exponent h
  rw [Fp.sqrt, ite_eq_left (beq_iff'.mpr hcand)]

/-! ## Big-endian byte recovery

`Fp.toBytesBE` is definitionally the KZG codec's `intToBytesBE` at
width 48, whose decode-encode round-trip is already proved in
`Proofs.Kzg.Polynomials`; the only new content is converting the
spec's `Id.run` decoding loop (`Fp.bytesBEToNat`) into the KZG
list-fold decoder. -/

private theorem byteArray_getElem! (b : ByteArray) (i : Nat) :
    b[i]! = b.data[i]! := by
  by_cases h : i < b.size
  · rw [getElem!_pos b i h, getElem!_pos b.data i h]
    rfl
  · rw [getElem!_neg b i h, getElem!_neg b.data i h]

open EthLib.Cryptography.IdLoops in
/-- The spec's byte-decoding loop, as a fold over the byte list. -/
private theorem bytesBEToNat_eq_list (b : ByteArray) :
    Fp.bytesBEToNat b
      = b.data.toList.foldl (fun acc u => (acc <<< 8) ||| u.toNat) 0 := by
  unfold Fp.bytesBEToNat
  dsimp only [Id.run, id_pure, id_bind]
  rw [forIn_range_yield]
  rw [show (fun (acc : Nat) (i : Nat) => (acc <<< 8) ||| b[i]!.toNat)
      = fun acc i => (acc <<< 8) ||| b.data[i]!.toNat from
      funext fun acc => funext fun i => by rw [byteArray_getElem!]]
  show (List.range' 0 b.data.size).foldl
      (fun acc i => (acc <<< 8) ||| b.data[i]!.toNat) 0 = _
  exact foldl_range'_getElem! b.data (fun acc u => (acc <<< 8) ||| u.toNat) 0

/-- The KZG list-fold decoder agrees with `List.foldl`. -/
private theorem kzgAux_eq_foldl (l : List UInt8) (acc : Nat) :
    Kzg.bytesBEToNatAux acc l
      = l.foldl (fun acc u => (acc <<< 8) ||| u.toNat) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons u rest ih =>
    rw [Kzg.bytesBEToNatAux, List.foldl_cons]
    exact ih _

/-- Decoding the encoding of a field element recovers its value. -/
private theorem bytesBEToNat_toBytesBE (x : Fp) :
    Fp.bytesBEToNat (Fp.toBytesBE x) = x.val := by
  have heq : Fp.toBytesBE x = Kzg.intToBytesBE x.val 48 := rfl
  rw [heq, bytesBEToNat_eq_list, ← kzgAux_eq_foldl]
  have := Kzg.bytesBEToNat_intToBytesBE_of_lt
    (n := x.val) (len := 48) (by
      calc x.val < Fp.modulus := x.isLt
        _ < 256 ^ 48 := by decide)
  rwa [Kzg.bytesBEToNat] at this

/-! ## Encoding size, byte 0, and the `fromBytesBE` round-trip -/

theorem size_toBytesBE (x : Fp) : (Fp.toBytesBE x).size = 48 := by
  simp only [Fp.toBytesBE, ByteArray.size, Array.size_ofFn]

set_option maxHeartbeats 1000000 in
/-- Byte 0 (most significant) of the big-endian encoding, via `.get!`
(the form `compress` uses). -/
theorem get!_toBytesBE_zero (x : Fp) :
    ((Fp.toBytesBE x).get! 0).toNat = (x.val >>> (47 * 8)) &&& 0xff := by
  have hdata : (Fp.toBytesBE x).get! 0 = (Array.ofFn (n := 48) (fun j =>
      UInt8.ofNat ((x.val >>> ((47 - j.val) * 8)) &&& 0xff)))[0]! := rfl
  rw [hdata,
    getElem!_pos (Array.ofFn (n := 48) fun j =>
      UInt8.ofNat ((x.val >>> ((47 - j.val) * 8)) &&& 0xff)) 0
      (by rw [Array.size_ofFn]; decide),
    Array.getElem_ofFn, UInt8.toNat_ofNat',
    show (0xff : Nat) = 2 ^ 8 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod, Nat.and_two_pow_sub_one_eq_mod]
  norm_num

set_option exponentiation.threshold 400 in
/-- The most significant byte of a canonical field element has its top
three bits clear (`< 0x20`), since `p < 2^381 = 32·2^376`. -/
theorem toBytesBE_head_lt (x : Fp) : ((Fp.toBytesBE x).get! 0).toNat < 0x20 := by
  rw [get!_toBytesBE_zero]
  have hb : x.val < 32 * 2 ^ (47 * 8) := lt_of_lt_of_le x.isLt (by decide)
  have hsr : x.val >>> (47 * 8) < 32 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hb)
  have hand : (x.val >>> (47 * 8)) &&& 0xff ≤ x.val >>> (47 * 8) := Nat.and_le_left
  omega

theorem fromBytesBE_toBytesBE (x : Fp) : Fp.fromBytesBE x.toBytesBE = .ok x := by
  rw [Fp.fromBytesBE, ite_eq_right (by rw [size_toBytesBE]; decide),
    dite_eq_left (by rw [bytesBEToNat_toBytesBE]; exact x.isLt)]
  congr 1
  apply Fin.ext
  exact bytesBEToNat_toBytesBE x

/-! ## Canonical byte encoding

A field element has exactly one 48-byte encoding.
Decoding rejects every value at or above `p`, and big-endian bytes of a fixed length have no slack.
-/

/-- Encoding a decoded field element gives back the input bytes. -/
theorem toBytesBE_fromBytesBE {b : ByteArray} {x : Fp}
    (h : Fp.fromBytesBE b = .ok x) : Fp.toBytesBE x = b := by
  rw [Fp.fromBytesBE] at h
  split at h
  -- A size other than 48 is rejected, so it cannot produce a field element.
  · cases h
  · rename_i hsz
    have hsz48 : b.size = 48 := by omega
    dsimp only at h
    split at h
    -- An in-range value is the decoded element itself.
    · cases h
      -- The encoder is the KZG big-endian encoder at width 48.
      -- The decoding loop is the KZG list fold over the same bytes.
      show Kzg.intToBytesBE (Fp.bytesBEToNat b) 48 = b
      rw [bytesBEToNat_eq_list, ← kzgAux_eq_foldl, ← hsz48]
      -- Any byte array is the encoding of its own value at its own size.
      exact Kzg.intToBytesBE_bytesBEToNat b
    -- A value at or above p is rejected.
    · cases h

end EthLib.Cryptography.Bls.Fp


namespace EthLib.Cryptography.Bls.G1

open WeierstrassCurve.Jacobian
open scoped EthLib.Cryptography.Bls.Fp

set_option maxRecDepth 4000

/-! ## Affine coordinates satisfy the curve equation -/

/-- Pure `ZMod` curve identity whose term structure matches `toAffine`
and uncompress's `rhs`, so it transfers to the spec goal by `exact`
(defeq: `Fin`-mul ≡ `ZMod`-mul). -/
private theorem curve_eq_aux (x y z w : ZMod Fp.modulus) (hw : z * w = 1)
    (heq : y ^ 2 = x ^ 3 + 4 * z ^ 6) :
    (y * (w * w * w)) * (y * (w * w * w))
      = x * (w * w) * (x * (w * w)) * (x * (w * w)) + 4 := by
  have h6 : (z * w) ^ 6 = 1 := by rw [hw, one_pow]
  linear_combination w ^ 6 * heq + 4 * h6

private theorem z_mul_inverse {p : G1} (hz : ¬ p.z.isZero = true) :
    (p.z : ZMod Fp.modulus) * (p.z.inverse : ZMod Fp.modulus) = 1 := by
  rw [Fp.inverse_eq_inv]
  exact mul_inv_cancel₀ (fun hh => hz (isZero_iff.mpr hh))

/-- The affine `y` squares to `x³ + 4` (matching uncompress's `rhs`). -/
theorem affine_sqrt_witness {p : G1} (h : Valid p) (hz : ¬ p.z.isZero = true) :
    ((p.toAffine).2 : ZMod Fp.modulus) * (p.toAffine).2
      = (p.toAffine).1 * (p.toAffine).1 * (p.toAffine).1 + Fp.ofNat 4 := by
  have heq := valid_equation h
  rw [rep_x, rep_y, rep_z] at heq
  have hw := z_mul_inverse hz
  simp only [G1.toAffine, ite_eq_right hz]
  exact curve_eq_aux p.x p.y p.z p.z.inverse hw heq

/-! ## Sign-bit recovery -/

/-- Sign bit flips under negation of a nonzero element (`p` is odd, so
`y ≠ p − y`). -/
theorem signBit_neg {y : Fp} (hy : y ≠ 0) :
    Fp.signBit (-y) = !Fp.signBit y := by
  have hv : (-y).val = Fp.modulus - y.val := by
    rw [Fin.val_neg, ite_eq_right hy]
  have hy0 : 0 < y.val := Nat.pos_of_ne_zero (fun hh => hy (Fin.ext hh))
  have hylt : y.val < Fp.modulus := y.isLt
  have hodd : Fp.modulus % 2 = 1 := by decide
  unfold Fp.signBit
  rw [hv, show Fp.modulus - (Fp.modulus - y.val) = y.val from by omega]
  rcases Nat.lt_trichotomy y.val (Fp.modulus - y.val) with h | h | h
  · rw [decide_eq_true (show Fp.modulus - y.val > y.val by omega),
      decide_eq_false (show ¬ y.val > Fp.modulus - y.val by omega), Bool.not_false]
  · omega
  · rw [decide_eq_false (show ¬ Fp.modulus - y.val > y.val by omega),
      decide_eq_true (show y.val > Fp.modulus - y.val by omega), Bool.not_true]

/-! ## The two square roots -/

/-- `yPos = ±ya`: any square root of `ya²` is `ya` or `-ya`
(`ZMod Fp.modulus` is a domain, as `p` is prime). -/
private theorem sqrt_pm {ya yPos : ZMod Fp.modulus}
    (h : yPos * yPos = ya * ya) : yPos = ya ∨ yPos = -ya := by
  have hfac : (yPos - ya) * (yPos + ya) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h2)

/-- Uncompress's sign selection recovers the original `y` from `±y`
and the stored sign bit. -/
private theorem sign_recovery {ya yPos : Fp}
    (hsq : (yPos : ZMod Fp.modulus) * yPos = (ya : ZMod Fp.modulus) * ya) :
    (if Fp.signBit yPos = Fp.signBit ya then yPos else -yPos) = ya := by
  rcases sqrt_pm hsq with h | h
  · rw [show yPos = ya from h, ite_eq_left rfl]
  · rw [show yPos = -ya from h]
    by_cases hya : ya = 0
    · subst hya
      simp
    · rw [signBit_neg hya, ite_eq_right (Bool.not_ne_self _), neg_neg]

/-! ## `ByteArray` `get!`/`set!` plumbing -/

private theorem ba_size_set! (b : ByteArray) (j : Nat) (v : UInt8) :
    (b.set! j v).size = b.size := Array.size_setIfInBounds

private theorem ba_get!_set!_ne (b : ByteArray) {i j : Nat} (v : UInt8)
    (hne : i ≠ j) : (b.set! j v).get! i = b.get! i := by
  show (b.data.setIfInBounds j v)[i]! = b.data[i]!
  by_cases hi : i < b.data.size
  · rw [getElem!_pos (b.data.setIfInBounds j v) i
        (by rw [Array.size_setIfInBounds]; exact hi),
      getElem!_pos b.data i hi, Array.getElem_setIfInBounds_ne hi (fun hh => hne hh.symm)]
  · rw [getElem!_neg (b.data.setIfInBounds j v) i
        (by rw [Array.size_setIfInBounds]; exact hi),
      getElem!_neg b.data i hi]

private theorem ba_get!_set!_self (b : ByteArray) {j : Nat} (v : UInt8)
    (hj : j < b.size) : (b.set! j v).get! j = v := by
  show (b.data.setIfInBounds j v)[j]! = v
  rw [getElem!_pos (b.data.setIfInBounds j v) j
    (by rw [Array.size_setIfInBounds]; exact hj), Array.getElem_setIfInBounds_self]

private theorem ba_ext {a b : ByteArray} (hsz : a.size = b.size)
    (h : ∀ i, i < a.size → a.get! i = b.get! i) : a = b := by
  apply ByteArray.ext
  apply Array.ext hsz
  intro i hi1 hi2
  have := h i hi1
  rwa [show a.get! i = a.data[i]! from rfl, show b.get! i = b.data[i]! from rfl,
    getElem!_pos a.data i hi1, getElem!_pos b.data i hi2] at this

/-! ## `toPoint` of the affine normalization -/

private theorem xval_aux (x z w : ZMod Fp.modulus) (hw : z * w = 1) :
    x * (w * w) * z ^ 2 = x := by linear_combination x * (z * w + 1) * hw

private theorem yval_aux (y z w : ZMod Fp.modulus) (hw : z * w = 1) :
    y * (w * w * w) * z ^ 3 = y := by
  linear_combination y * ((z * w) ^ 2 + z * w + 1) * hw

private theorem xeq_aux (x z w one : ZMod Fp.modulus) (hw : z * w = 1)
    (hone : one = 1) : x * (w * w) * z ^ 2 = x * one ^ 2 := by
  subst hone; rw [one_pow, mul_one]; exact xval_aux x z w hw

private theorem yeq_aux (y z w one : ZMod Fp.modulus) (hw : z * w = 1)
    (hone : one = 1) : y * (w * w * w) * z ^ 3 = y * one ^ 3 := by
  subst hone; rw [one_pow, mul_one]; exact yval_aux y z w hw

/-- The compressed-then-decompressed point (affine, `z = 1`) denotes the
same group element as `p`. -/
theorem toPoint_affine_normalize {p : G1} (hz : ¬ p.z.isZero = true) :
    toPoint ⟨(p.toAffine).1, (p.toAffine).2, Fp.one⟩ = toPoint p := by
  have hzne : (p.z : ZMod Fp.modulus) ≠ 0 := fun hh => hz (isZero_iff.mpr hh)
  have hw := z_mul_inverse hz
  refine Point.toAffine_of_equiv (equiv_of_X_eq_of_Y_eq one_ne_zero hzne ?_ ?_)
  · -- rep q 0 * rep p 2 ^ 2 = rep p 0 * rep q 2 ^ 2
    simp only [rep, G1.toAffine, ite_eq_right hz]
    exact xeq_aux p.x p.z p.z.inverse Fp.one hw rfl
  · simp only [rep, G1.toAffine, ite_eq_right hz]
    exact yeq_aux p.y p.z p.z.inverse Fp.one hw rfl

/-! ## Compress → uncompress round-trip -/

private theorem compress_inf {p : G1} (hinf : p.isInfinity = true) :
    compress p = infinityBytes := by
  unfold compress; simp only [Id.run, hinf, ite_true]; rfl

private theorem compress_noninf {p : G1} (hinf : ¬ p.isInfinity = true)
    {xa ya : Fp} (hpa : p.toAffine = (xa, ya)) :
    compress p =
      (let base := (Fp.toBytesBE xa).set! 0 ((Fp.toBytesBE xa).get! 0 ||| 0x80)
       if Fp.signBit ya then base.set! 0 (base.get! 0 ||| 0x20) else base) := by
  unfold compress
  simp only [Id.run, hinf, hpa]
  rfl

/-- The infinity round-trip is a closed 48-byte decidable computation
checked in the kernel (`decide +kernel`). -/
private theorem uncompress_infinityBytes :
    uncompress infinityBytes = .ok zero := by decide +kernel

/-- Sign selection in `uncompress` (a `Prop`-equality condition)
recovers `y` from `±y` and the stored sign bit. -/
private theorem sign_recovery' {ya yPos : Fp} {P : Prop} [Decidable P]
    (hsq : (yPos : ZMod Fp.modulus) * yPos = (ya : ZMod Fp.modulus) * ya)
    (hP : P ↔ (Fp.signBit ya = true)) :
    (if (Fp.signBit yPos = true) = P then yPos else -yPos) = ya := by
  have key : ((Fp.signBit yPos = true) = P) ↔ (Fp.signBit yPos = Fp.signBit ya) := by
    rw [eq_iff_iff, hP]
    by_cases h1 : Fp.signBit yPos = true <;> by_cases h2 : Fp.signBit ya = true <;>
      simp_all
  rw [if_congr key rfl rfl]
  exact sign_recovery hsq

/-- Uncompress recovers `⟨xa, ya, 1⟩` from compressed bytes `cb`
satisfying the flag- and coordinate-level facts. -/
private theorem uncompress_of_facts {xa ya yPos : Fp} {cb : ByteArray}
    (hsize : cb.size = 48)
    (hc : (cb.get! 0 &&& 0x80) ≠ 0)
    (hi : (cb.get! 0 &&& 0x40) = 0)
    (hsg : (cb.get! 0 &&& 0x20 ≠ 0) ↔ (Fp.signBit ya = true))
    (hmaskeq : cb.set! 0 (cb.get! 0 &&& 0x1f) = Fp.toBytesBE xa)
    (hsqrt : Fp.sqrt (xa * xa * xa + Fp.ofNat 4) = .ok yPos)
    (hysq : (yPos : ZMod Fp.modulus) * yPos = (ya : ZMod Fp.modulus) * ya) :
    uncompress cb = .ok ⟨xa, ya, Fp.one⟩ := by
  rw [uncompress, ite_eq_right (by rw [hsize]; decide)]
  simp only
  rw [ite_eq_right (by rw [decide_eq_true hc]; decide), ite_eq_right (by rw [hi]; decide),
    hmaskeq, Fp.fromBytesBE_toBytesBE]
  simp only [hsqrt]
  rw [sign_recovery' hysq hsg]

/-! ## Flags in the compressed header byte

Byte 0 of a compressed point carries three flags above the five high bits of `x`.

```text
    bit    7            6          5      4 3 2 1 0
         [ compressed | infinity | sign | high bits of x ]
           0x80         0x40       0x20   0x1f
```

A canonical `x` is below `2^381`, so its top byte is below `0x20` and never overlaps the flags.

Each lemma below reads one field back from the byte that compression writes.
-/

/-- Compression with the sign set keeps the compression flag readable. -/
private theorem b0_pos_c (B0 : UInt8) :
    (B0 ||| 0x80 ||| 0x20) &&& 0x80 ≠ 0 := by
  -- Check all 256 byte values in the kernel.
  rcases B0 with ⟨⟨i⟩⟩; revert i; decide

/-- Compression with the sign set leaves the infinity flag clear. -/
private theorem b0_pos_i (B0 : UInt8) (hb0 : B0 < 0x20) :
    (B0 ||| 0x80 ||| 0x20) &&& 0x40 = 0 := by
  -- Check all 256 byte values in the kernel, where values from 0x20 up hold vacuously.
  rcases B0 with ⟨⟨i⟩⟩; revert i hb0; decide

/-- Compression with the sign set makes the sign flag readable. -/
private theorem b0_pos_s (B0 : UInt8) :
    (B0 ||| 0x80 ||| 0x20) &&& 0x20 ≠ 0 := by
  -- Check all 256 byte values in the kernel.
  rcases B0 with ⟨⟨i⟩⟩; revert i; decide

/-- Compression with the sign set keeps the five high bits of `x` readable. -/
private theorem b0_pos_m (B0 : UInt8) (hb0 : B0 < 0x20) :
    (B0 ||| 0x80 ||| 0x20) &&& 0x1f = B0 := by
  -- Check all 256 byte values in the kernel, where values from 0x20 up hold vacuously.
  rcases B0 with ⟨⟨i⟩⟩; revert i hb0; decide

/-- Compression with the sign clear keeps the compression flag readable. -/
private theorem b0_neg_c (B0 : UInt8) :
    (B0 ||| 0x80) &&& 0x80 ≠ 0 := by
  -- Check all 256 byte values in the kernel.
  rcases B0 with ⟨⟨i⟩⟩; revert i; decide

/-- Compression with the sign clear leaves the infinity flag clear. -/
private theorem b0_neg_i (B0 : UInt8) (hb0 : B0 < 0x20) :
    (B0 ||| 0x80) &&& 0x40 = 0 := by
  -- Check all 256 byte values in the kernel, where values from 0x20 up hold vacuously.
  rcases B0 with ⟨⟨i⟩⟩; revert i hb0; decide

/-- Compression with the sign clear leaves the sign flag clear. -/
private theorem b0_neg_s (B0 : UInt8) (hb0 : B0 < 0x20) :
    (B0 ||| 0x80) &&& 0x20 = 0 := by
  -- Check all 256 byte values in the kernel, where values from 0x20 up hold vacuously.
  rcases B0 with ⟨⟨i⟩⟩; revert i hb0; decide

/-- Compression with the sign clear keeps the five high bits of `x` readable. -/
private theorem b0_neg_m (B0 : UInt8) (hb0 : B0 < 0x20) :
    (B0 ||| 0x80) &&& 0x1f = B0 := by
  -- Check all 256 byte values in the kernel, where values from 0x20 up hold vacuously.
  rcases B0 with ⟨⟨i⟩⟩; revert i hb0; decide

/-- **Compression round-trip.** For any valid point `p`, `compress`
followed by `uncompress` succeeds and returns a point `q` denoting the
same group element (`toPoint q = toPoint p`). The Jacobian
representative is generally *not* preserved — `compress` records only
the affine `x` plus the sign of `y`, so decompression rebuilds the
canonical `z = 1` representative — but the underlying curve point is.
This is the encoding half of the BLS G1 serialization spec; it relies
on `p` being prime (both square roots are `±y`, recovered via the
stored sign bit) and on `p ≡ 3 (mod 4)` (so `Fp.sqrt` is exact). -/
theorem uncompress_compress {p : G1} (h : Valid p) :
    ∃ q, uncompress (compress p) = .ok q ∧ toPoint q = toPoint p := by
  by_cases hinf : p.isInfinity = true
  · refine ⟨zero, ?_, ?_⟩
    · rw [compress_inf hinf]; exact uncompress_infinityBytes
    · rw [toPoint_zero]
      exact (Point.toAffine_of_Z_eq_zero (W := curve)
        (isZero_iff.mp hinf : rep p 2 = 0)).symm
  · rcases hpa : p.toAffine with ⟨xa, ya⟩
    set B0 := (Fp.toBytesBE xa).get! 0 with hB0
    have hb0 : B0 < 0x20 := by
      rw [hB0, UInt8.lt_iff_toNat_lt]; exact Fp.toBytesBE_head_lt xa
    have hsqw : (ya : ZMod Fp.modulus) * ya = xa * xa * xa + Fp.ofNat 4 := by
      have := affine_sqrt_witness h hinf; rw [hpa] at this; exact this
    have hsqrt := Fp.sqrt_complete hsqw
    have hysq : ((Fp.powNat (xa * xa * xa + Fp.ofNat 4)
        ((Fp.modulus + 1) / 4) : Fp) : ZMod Fp.modulus)
        * Fp.powNat (xa * xa * xa + Fp.ofNat 4) ((Fp.modulus + 1) / 4)
        = (ya : ZMod Fp.modulus) * ya := by rw [Fp.sqrt_ok hsqrt, ← hsqw]
    have hsz48 : (Fp.toBytesBE xa).size = 48 := Fp.size_toBytesBE xa
    have hcp := compress_noninf hinf hpa
    have hother : ∀ i, i ≠ 0 → (compress p).get! i = (Fp.toBytesBE xa).get! i := by
      intro i hi0
      rw [hcp]; dsimp only
      by_cases hs : Fp.signBit ya
      · rw [ite_eq_left hs, ba_get!_set!_ne _ _ hi0, ba_get!_set!_ne _ _ hi0]
      · rw [ite_eq_right hs, ba_get!_set!_ne _ _ hi0]
    have hsize : (compress p).size = 48 := by
      rw [hcp]; dsimp only
      by_cases hs : Fp.signBit ya
      · rw [ite_eq_left hs, ba_size_set!, ba_size_set!, hsz48]
      · rw [ite_eq_right hs, ba_size_set!, hsz48]
    refine ⟨⟨xa, ya, Fp.one⟩, ?_, ?_⟩
    · by_cases hs : Fp.signBit ya
      · have hhead : (compress p).get! 0 = B0 ||| 0x80 ||| 0x20 := by
          rw [hcp]; dsimp only
          rw [ite_eq_left hs, ba_get!_set!_self _ _ (by rw [ba_size_set!, hsz48]; decide),
            ba_get!_set!_self _ _ (by rw [hsz48]; decide)]
        refine uncompress_of_facts hsize (by rw [hhead]; exact b0_pos_c B0)
          (by rw [hhead]; exact b0_pos_i B0 hb0) ?_ ?_ hsqrt hysq
        · rw [hhead]
          exact ⟨fun _ => hs, fun _ => b0_pos_s B0⟩
        · refine ba_ext (by rw [ba_size_set!, hsize, hsz48]) (fun i hi' => ?_)
          rw [ba_size_set!, hsize] at hi'
          by_cases hi0 : i = 0
          · subst hi0
            rw [ba_get!_set!_self _ _ (by rw [hsize]; decide), hhead, ← hB0]
            exact b0_pos_m B0 hb0
          · rw [ba_get!_set!_ne _ _ hi0, hother i hi0]
      · have hhead : (compress p).get! 0 = B0 ||| 0x80 := by
          rw [hcp]; dsimp only
          rw [ite_eq_right hs, ba_get!_set!_self _ _ (by rw [hsz48]; decide)]
        refine uncompress_of_facts hsize (by rw [hhead]; exact b0_neg_c B0)
          (by rw [hhead]; exact b0_neg_i B0 hb0) ?_ ?_ hsqrt hysq
        · rw [hhead]
          exact ⟨fun hne => absurd (b0_neg_s B0 hb0) hne, fun hh => absurd hh hs⟩
        · refine ba_ext (by rw [ba_size_set!, hsize, hsz48]) (fun i hi' => ?_)
          rw [ba_size_set!, hsize] at hi'
          by_cases hi0 : i = 0
          · subst hi0
            rw [ba_get!_set!_self _ _ (by rw [hsize]; decide), hhead, ← hB0]
            exact b0_neg_m B0 hb0
          · rw [ba_get!_set!_ne _ _ hi0, hother i hi0]
    · have := toPoint_affine_normalize (p := p) hinf
      rw [hpa] at this; exact this

/-! ## Converse round-trip: every accepted encoding is canonical

Decompression followed by compression returns the input bytes.

So two different byte strings never decode to the same point.

The proof rests on three facts:

- A field element has exactly one 48-byte encoding.
- No point on the curve has `y = 0`, so the sign bit always picks one of two distinct roots.
- The point at infinity is accepted only as `0xc0` followed by 47 zero bytes.
-/

/-! ### No curve point has `y = 0` -/

set_option maxRecDepth 8000 in
set_option exponentiation.threshold 512 in
/-- The equation `x^3 + 4 = 0` has no solution modulo `p`.

Equivalently, `-4` is not a cube modulo `p`.

# Why it holds

- `p - 1` is divisible by 3, so the cubes form a subgroup of index 3 in the nonzero residues.
- By Euler's criterion for cubes, `a` is a cube if and only if `a^((p - 1) / 3) = 1`.
- The kernel evaluates `(-4)^((p - 1) / 3) mod p` and finds a value other than 1.
-/
private theorem cube_add_four_ne_zero_zmod (x : ZMod Fp.modulus) :
    x * x * x + 4 ≠ 0 := by
  intro h
  -- Rewrite the root as a cube: x^3 = -4, with -4 written as the natural number p - 4.
  have h3 : x ^ 3 = ((Fp.modulus - 4 : Nat) : ZMod Fp.modulus) := by
    have h4 : (-4 : ZMod Fp.modulus) = ((Fp.modulus - 4 : Nat) : ZMod Fp.modulus) := by decide
    rw [← h4]
    linear_combination h
  -- x = 0 would give 4 = 0, which fails modulo p.
  have hx : x ≠ 0 := by
    intro hx0
    rw [hx0] at h
    revert h; decide
  -- Fermat's little theorem: x^(p - 1) = 1 for nonzero x.
  have hfermat : x ^ (Fp.modulus - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one hx
  -- Group the exponent as 3 * ((p - 1) / 3), so x^(p - 1) = (x^3)^((p - 1) / 3) = (-4)^((p - 1) / 3).
  rw [show Fp.modulus - 1 = 3 * ((Fp.modulus - 1) / 3) by decide,
    pow_mul, h3] at hfermat
  -- The kernel computes (-4)^((p - 1) / 3) mod p by square-and-multiply and finds it is not 1.
  exact PowMod.natCast_pow_div_ne_one Fp.modulus 384 (Fp.modulus - 4) 3
    (by decide) (by decide) hfermat

/-- The curve right-hand side `x^3 + 4` never vanishes over the base field.

So every point on the curve `y^2 = x^3 + 4` has `y != 0`.

This makes the two square roots `y` and `-y` distinct, so the sign bit of a compressed point always selects exactly one of them.
-/
theorem cube_add_four_ne_zero (x : Fp) :
    (x : ZMod Fp.modulus) * x * x + Fp.ofNat 4 ≠ 0 :=
  -- The base field is the integers modulo p, where the statement is proved above.
  cube_add_four_ne_zero_zmod x

/-! ### Decoded points lie on the curve -/

/-- The curve equation in the general Weierstrass form, for `z = 1` and `a_1 = a_2 = a_3 = a_4 = 0`. -/
private theorem valid_eq_zmod {x y : ZMod Fp.modulus} (h : y * y = x * x * x + 4) :
    y ^ 2 + 0 * x * y * 1 + 0 * y * 1 ^ 3 - (x ^ 3 + 0 * x ^ 2 * 1 ^ 2 + 0 * x * 1 ^ 4 + 4 * 1 ^ 6) = 0 := by
  -- Every term with a zero coefficient drops, leaving y^2 - (x^3 + 4) = 0.
  linear_combination h

/-- The partial derivative in `y`, which is `2 * y`, is nonzero at every curve point.

That alone makes the point nonsingular.
-/
private theorem dy_ne_zero_zmod {x y : ZMod Fp.modulus} (h : y * y = x * x * x + 4) :
    2 * y + 0 * x * 1 + 0 * 1 ^ 3 ≠ 0 := by
  intro hdy
  -- y^2 = x^3 + 4 is nonzero, so y is nonzero.
  have hy2 : y * y ≠ 0 := by
    rw [h]
    exact cube_add_four_ne_zero_zmod x
  have hy : y ≠ 0 := fun hy0 => hy2 (by rw [hy0, mul_zero])
  -- p is odd, so 2 is invertible.
  have h2 : (2 : ZMod Fp.modulus) ≠ 0 := by decide
  -- A product of two nonzero field elements is nonzero, contradicting 2 * y = 0.
  have hdy' : (2 : ZMod Fp.modulus) * y = 0 := by linear_combination hdy
  exact mul_ne_zero h2 hy hdy'

/-- A pair `(x, y)` with `y^2 = x^3 + 4` gives a nonsingular point with `z = 1`. -/
private theorem valid_of_affine_eq {x y : Fp}
    (h : (y : ZMod Fp.modulus) * y = x * x * x + Fp.ofNat 4) :
    Valid ⟨x, y, Fp.one⟩ := by
  show curve.Nonsingular (rep ⟨x, y, Fp.one⟩)
  -- Nonsingular means: the equation holds and some partial derivative is nonzero.
  rw [nonsingular_iff, equation_iff]
  -- Substitute the curve coefficients (all zero except a_6 = 4) and z = 1.
  simp only [show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
    show curve.a₃ = 0 from rfl, show curve.a₄ = 0 from rfl,
    show curve.a₆ = (4 : ZMod Fp.modulus) from rfl,
    rep_x, rep_y, rep_z, show (Fp.one : ZMod Fp.modulus) = 1 from rfl]
  -- The equation holds, and the y-derivative is the nonzero partial.
  exact ⟨valid_eq_zmod h, Or.inr (Or.inl (dy_ne_zero_zmod h))⟩

/-- Choosing `y` or `-y` does not change `y^2`. -/
private theorem sq_select {yPos : Fp} {P : Prop} [Decidable P] :
    (((if (Fp.signBit yPos = true) = P then yPos else -yPos : Fp) : ZMod Fp.modulus) *
      (if (Fp.signBit yPos = true) = P then yPos else -yPos : Fp)) =
      (yPos : ZMod Fp.modulus) * yPos := by
  split
  -- Keeping the root leaves the square unchanged.
  · rfl
  -- Negating the root: (-y) * (-y) = y * y.
  · exact neg_mul_neg _ _

/-- Any point returned by decompression is a nonsingular curve point.

Decompression does not check subgroup membership, so neither does this statement.
-/
theorem uncompress_valid {b : ByteArray} {q : G1}
    (h : G1.uncompress b = .ok q) : Valid q := by
  rw [uncompress] at h
  split at h
  -- A size other than 48 is rejected.
  · cases h
  · dsimp only at h
    split at h
    -- A cleared compression flag is rejected.
    · cases h
    · split at h
      -- Infinity flag set: the result, if any, is the identity, which is valid.
      · split at h
        · cases h
        · cases h
          exact valid_zero
      -- Infinity flag clear: x must decode and x^3 + 4 must have a square root.
      · split at h
        · cases h
        · rename_i x hx
          split at h
          · cases h
          · rename_i yPos hsqrt
            cases h
            -- The returned point is (x, y, 1) with y = yPos or y = -yPos.
            apply valid_of_affine_eq
            -- Either sign squares to yPos^2, and the square root guarantees yPos^2 = x^3 + 4.
            rw [sq_select]
            exact Fp.sqrt_ok hsqrt

/-! ### Re-encoding the header byte -/

/-- The sign bit of the chosen root is exactly the requested sign.

Decompression keeps the computed root when its sign already matches, and negates it otherwise.
Negating a nonzero element flips its sign bit, so the result always carries the requested sign.
-/
private theorem signBit_select {yPos : Fp} (hypos : yPos ≠ 0)
    {P : Prop} [Decidable P] :
    Fp.signBit (if (Fp.signBit yPos = true) = P then yPos else -yPos)
      = decide P := by
  -- Four cases: the requested sign, times the sign of the computed root.
  by_cases hP : P <;> by_cases hs : Fp.signBit yPos = true
  -- Signs agree: keep the root.
  · rw [ite_eq_left (by simp [hP, hs]), hs, decide_eq_true hP]
  -- Signs differ: negate the root, which flips its sign bit.
  · rw [ite_eq_right (by simp [hP, hs]), signBit_neg hypos,
      Bool.eq_false_iff.mpr hs, Bool.not_false, decide_eq_true hP]
  · rw [ite_eq_right (by simp [hP, hs]), signBit_neg hypos, hs,
      Bool.not_true, decide_eq_false hP]
  -- Signs agree: keep the root.
  · rw [ite_eq_left (by simp [hP, hs]), Bool.eq_false_iff.mpr hs, decide_eq_false hP]

/-- A compressed header byte is rebuilt from its five low bits and its sign flag.

The byte must have the compression flag set and the infinity flag clear.

```text
    head            = 1 0 s x x x x x
    head &&& 0x1f   = 0 0 0 x x x x x
    | 0x80          = 1 0 0 x x x x x
    | 0x20 (if s)   = 1 0 s x x x x x  = head
```
-/
private theorem head_reconstruct (head : UInt8)
    (hc : (head &&& 0x80) ≠ 0) (hi : (head &&& 0x40) = 0) :
    (if (head &&& 0x20) ≠ 0 then (head &&& 0x1f) ||| 0x80 ||| 0x20
     else (head &&& 0x1f) ||| 0x80) = head := by
  -- Check all 256 byte values in the kernel.
  rcases head with ⟨⟨i⟩⟩; revert i hc hi; decide

/-- Writing the same position twice keeps only the second write. -/
private theorem ba_set!_set!_same (b : ByteArray) (j : Nat) (u v : UInt8) :
    (b.set! j u).set! j v = b.set! j v := by
  -- Compare the two arrays byte by byte.
  refine ba_ext (by rw [ba_size_set!, ba_size_set!, ba_size_set!]) (fun i hi => ?_)
  rw [ba_size_set!, ba_size_set!] at hi
  by_cases hij : i = j
  -- At the written position both sides hold the second value.
  · subst hij
    rw [ba_get!_set!_self _ _ (by rw [ba_size_set!]; exact hi),
      ba_get!_set!_self _ _ hi]
  -- Elsewhere both sides hold the original byte.
  · rw [ba_get!_set!_ne _ _ hij, ba_get!_set!_ne _ _ hij, ba_get!_set!_ne _ _ hij]

/-- Writing a byte back to where it was read leaves the array unchanged. -/
private theorem ba_set!_get!_self (b : ByteArray) {j : Nat} (hj : j < b.size) :
    b.set! j (b.get! j) = b := by
  -- Compare the two arrays byte by byte.
  refine ba_ext (ba_size_set! b j _) (fun i hi => ?_)
  rw [ba_size_set!] at hi
  by_cases hij : i = j
  -- At the written position the new byte is the old byte.
  · subst hij; exact ba_get!_set!_self b _ hj
  -- Elsewhere nothing changed.
  · exact ba_get!_set!_ne b _ hij

/-- A point with `z = 1` is already affine. -/
private theorem toAffine_of_z_one (x y : Fp) :
    (⟨x, y, Fp.one⟩ : G1).toAffine = (x, y) := by
  unfold toAffine
  -- z = 1 is not zero, so the point is not at infinity.
  rw [ite_eq_right (by decide : ¬ Fp.one.isZero = true)]
  -- The inverse of 1 is 1, read off from the identity z * z^(-1) = 1.
  have hinv : Fp.one.inverse = (1 : Fp) := by
    have h := z_mul_inverse (p := ⟨Fp.zero, Fp.zero, Fp.one⟩) (by decide)
    change (1 : Fp) * Fp.one.inverse = (1 : Fp) at h
    rwa [Fin.one_mul] at h
  -- Dividing by 1^2 and 1^3 leaves x and y unchanged.
  dsimp only
  rw [hinv, Fin.mul_one, Fin.mul_one, Fin.mul_one, Fin.mul_one]

/-! ### The infinity encoding -/

/-- A fold that clears a flag on any nonzero byte ends true only if every byte it visits is zero. -/
private theorem foldl_allZero (b : ByteArray) (s n : Nat) (init : Bool)
    (h : (List.range' s n).foldl
      (fun ok i => if b.get! i ≠ 0 then false else ok) init = true) :
    init = true ∧ ∀ i, s ≤ i → i < s + n → b.get! i = 0 := by
  induction n generalizing s init with
  -- No positions visited: the flag is its initial value.
  | zero => exact ⟨h, fun i h1 h2 => by omega⟩
  | succ n ih =>
    -- Peel off position s, then apply the induction hypothesis to positions s + 1 onwards.
    rw [List.range'_succ, List.foldl_cons] at h
    obtain ⟨hinit, hrest⟩ := ih (s + 1) _ h
    -- A nonzero byte at s would clear the flag, and nothing sets it again.
    have hs : b.get! s = 0 := by
      by_contra hne
      rw [ite_eq_left hne] at hinit
      cases hinit
    -- Position s is zero, and the flag passed through it unchanged.
    refine ⟨by rwa [ite_eq_right (not_not.mpr hs)] at hinit, fun i h1 h2 => ?_⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact hs
    · exact hrest i hlt (by omega)

open EthLib.Cryptography.IdLoops in
/-- The tail scan in decompression succeeds only if bytes `1` to the end are all zero. -/
private theorem tailAllZero_ok (b : ByteArray)
    (h : (Id.run do
      let mut ok := true
      for i in [1 : b.size] do
        if b.get! i ≠ 0 then ok := false
      return ok) = true) :
    ∀ i, 1 ≤ i → i < b.size → b.get! i = 0 := by
  -- Turn the imperative loop over the range into a fold over the list of indices.
  dsimp only [Id.run, id_pure, id_bind] at h
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  -- Each loop step only continues, so the body is a plain fold step.
  have hbody : (fun (i : Nat) (ok : Bool) =>
      (if b.get! i ≠ 0 then ForInStep.yield false
        else ForInStep.yield ok : Id (ForInStep Bool)))
      = fun i ok => ForInStep.yield (if b.get! i ≠ 0 then false else ok) := by
    funext i ok; split <;> rfl
  change (forIn (m := Id) (List.range' 1 ([1 : b.size].size) 1) true
      (fun i ok => if b.get! i ≠ 0 then ForInStep.yield false else ForInStep.yield ok)) = true at h
  rw [hbody, forIn_list_yield] at h
  -- The range from 1 to the size visits size - 1 positions.
  have hsz : [1 : b.size].size = b.size - 1 := by
    simp [Std.Legacy.Range.size]
  rw [hsz] at h
  intro i hi1 hi2
  exact (foldl_allZero b 1 (b.size - 1) true h).2 i hi1 (by omega)

/-- Every byte of the infinity encoding after the first is zero. -/
private theorem infinityBytes_get!_pos (i : Fin 48) (hi : 1 ≤ i.val) :
    infinityBytes.get! i.val = 0 := by
  -- Check all 48 positions in the kernel.
  revert hi i; decide

/-- A point with `y = 0` would put a root of `x^3 + 4` on the curve. -/
private theorem zero_eq_of_sq_eq {x y : ZMod Fp.modulus} (hy0 : y = 0)
    (hsq : y * y = x * x * x + 4) : x * x * x + 4 = 0 := by
  -- Substitute y = 0 into y^2 = x^3 + 4.
  rw [hy0] at hsq
  linear_combination -hsq

/-! ### The converse theorems -/

/-- **Canonical decompression round-trip.**
Compressing any point that decompression returned gives back the exact 48 input bytes.

# Algorithm

Accepted inputs fall into two shapes, and each is rebuilt byte for byte.

```text
    infinity:   [ 0xc0 | 47 zero bytes ]          checked byte by byte on input
    finite:     [ 1 0 s x_top | 47 bytes of x ]   x canonical, s the sign of y
```

- Infinity: decompression accepts only the encoding that compression writes.
- Finite: the 48 bytes of `x` are its unique encoding, and the header byte is rebuilt from its sign bit.
-/
theorem compress_uncompress {b : ByteArray} {q : G1}
    (h : G1.uncompress b = .ok q) : G1.compress q = b := by
  rw [uncompress] at h
  split at h
  -- A size other than 48 is rejected.
  · cases h
  · rename_i hsz
    have hsz48 : b.size = 48 := by omega
    dsimp only at h
    split at h
    -- A cleared compression flag is rejected.
    · cases h
    · rename_i hcomp
      -- Invariant: the compression flag 0x80 is set in the header byte.
      have hc : (b.get! 0 &&& 0x80) ≠ 0 := by
        by_contra h0
        exact hcomp (by simp [h0])
      split at h
      -- Phase 1: infinity flag set.
      · split at h
        · cases h
        · rename_i hflags
          cases h
          -- Compressing the identity writes the fixed infinity encoding.
          rw [compress_inf rfl]
          -- Acceptance means: header byte 0xc0, and a successful tail scan.
          simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hflags
          obtain ⟨⟨_, hhead⟩, htail⟩ := hflags
          have hhead0 : b.get! 0 = 0xc0 := Classical.not_not.mp (of_decide_eq_false hhead)
          have htail0 : ∀ i, 1 ≤ i → i < b.size → b.get! i = 0 :=
            tailAllZero_ok b (by simp only [Bool.not_eq_false'] at htail; exact htail)
          -- Compare with the infinity encoding byte by byte.
          refine ba_ext (by rw [hsz48]; decide) (fun i hi => ?_)
          have hi48 : i < 48 := by simpa [show infinityBytes.size = 48 by decide] using hi
          by_cases hi0 : i = 0
          -- Byte 0 is 0xc0 on both sides.
          · subst hi0
            rw [hhead0]
            decide
          -- Bytes 1 to 47 are zero on both sides.
          · have hi1 : 1 ≤ i := Nat.pos_of_ne_zero hi0
            have hib : i < b.size := by rw [hsz48]; exact hi48
            rw [infinityBytes_get!_pos ⟨i, hi48⟩ hi1, htail0 i hi1 hib]
      -- Phase 2: infinity flag clear, so the point is finite.
      · rename_i hinf_flag
        -- Invariant: the infinity flag 0x40 is clear in the header byte.
        have hi : (b.get! 0 &&& 0x40) = 0 := not_ne_iff.mp hinf_flag
        split at h
        · cases h
        · rename_i x hx
          split at h
          · cases h
          · rename_i yPos hsqrt
            cases h
            -- Name the root that decompression selected from the sign flag.
            set y : Fp :=
              if (Fp.signBit yPos = true) = ((b.get! 0 &&& 0x20) ≠ 0) then yPos else -yPos
            -- The decoded point has z = 1, so it is finite and already affine.
            have hqinf : ¬ (⟨x, y, Fp.one⟩ : G1).isInfinity = true := by
              change ¬ Fp.one.isZero = true
              decide
            have hpa : (⟨x, y, Fp.one⟩ : G1).toAffine = (x, y) := toAffine_of_z_one x y
            rw [compress_noninf hqinf hpa]
            dsimp only
            -- x was decoded from the input with its flag bits cleared.
            -- Its encoding is therefore that same masked input.
            have hxbytes : Fp.toBytesBE x = b.set! 0 (b.get! 0 &&& 0x1f) :=
              Fp.toBytesBE_fromBytesBE hx
            -- The computed root is nonzero, because x^3 + 4 has no root.
            have hypos : yPos ≠ 0 := by
              intro hy0
              exact cube_add_four_ne_zero x (zero_eq_of_sq_eq hy0 (Fp.sqrt_ok hsqrt))
            -- So the selected root carries exactly the sign stored in the input.
            have hsign : Fp.signBit y = decide ((b.get! 0 &&& 0x20) ≠ 0) :=
              signBit_select hypos
            have h0lt : 0 < b.size := by omega
            -- Setting the compression flag on the masked input gives:
            --
            --     header byte (head &&& 0x1f) ||| 0x80, then 47 bytes of b
            have hbase :
                (Fp.toBytesBE x).set! 0 ((Fp.toBytesBE x).get! 0 ||| 0x80) =
                  b.set! 0 ((b.get! 0 &&& 0x1f) ||| 0x80) := by
              rw [hxbytes, ba_get!_set!_self b _ h0lt, ba_set!_set!_same]
            by_cases hs : (b.get! 0 &&& 0x20) ≠ 0
            -- Sign flag set: compression also sets 0x20, which rebuilds the header byte.
            · have hsy : Fp.signBit y = true := by rw [hsign, decide_eq_true hs]
              have hrec := head_reconstruct (b.get! 0) hc hi
              rw [ite_eq_left hs] at hrec
              rw [ite_eq_left hsy, hbase, ba_get!_set!_self b _ h0lt,
                ba_set!_set!_same, hrec, ba_set!_get!_self b h0lt]
            -- Sign flag clear: compression leaves 0x20 clear, which is the header byte.
            · have hsy : ¬ Fp.signBit y = true := by rw [hsign, decide_eq_false hs]; decide
              have hrec := head_reconstruct (b.get! 0) hc hi
              rw [ite_eq_right hs] at hrec
              rw [ite_eq_right hsy, hbase, hrec, ba_set!_get!_self b h0lt]

/-- **Non-malleability.** Two byte strings that decompress to the same point are equal.

A BLS public key or signature therefore has one byte representation.
So it can serve as an identifier, for example as a map key or a hash input.
-/
theorem uncompress_injective {b₁ b₂ : ByteArray} {q : G1}
    (h₁ : G1.uncompress b₁ = .ok q) (h₂ : G1.uncompress b₂ = .ok q) : b₁ = b₂ := by
  -- Both inputs are the compression of the same point.
  rw [← compress_uncompress h₁, compress_uncompress h₂]

end EthLib.Cryptography.Bls.G1
