module

public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Check

/-!
# Proofs: points of `G1` as naturals, for kernel checks of the setup

A kernel check that compares points of the embedded setup needs each point exactly.

The torsion check reads only `x`, since `-P` has the same order as `P`.

A comparison of points also needs `y`, with the sign that the encoding gives.

Here the coordinates are naturals below `p`, with the field operations of the torsion check.

So the check computes the same values as `Fp`, without reducing its representation.

- A string of 96 hexadecimal digits decodes to `(x, y)`, as decompression computes it.
  The sign flag picks the candidate root of `x^3 + 4` or its negation.
- A pair `(x, y)` below `p` with `y^2 = x^3 + 4` is a valid point with `z = 1`.
- A point `(X, Y, Z)` with `Z ≠ 0`, `X = x Z^2` and `Y = y Z^3` is the point `(x, y, 1)`.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

open EthLib.Cryptography.Bls
open EthLib.Cryptography.Bls.G1
open EthLib.Cryptography.Bls.G1.TorsionCheck (Coords coords fadd fmul rootCandidate)
open EthLib.Cryptography.Kzg.SetupTorsion (hexBytes xOf codes)
open WeierstrassCurve.Jacobian

/-! ## Decoding with the sign -/

/-- The right side `x^3 + 4` of the curve equation, mod `p`. -/
def rhs (x : Nat) : Nat := fadd (fmul (fmul x x) x) (4 % Fp.modulus)

/-- The sign of `y`, as the encoding defines it: `y` is greater than `p - y`. -/
def signBit (y : Nat) : Bool := y > Fp.modulus - y

/-- The affine point that 48 bytes encode.

The infinity flag, or an `x^3 + 4` that is not a square, gives `none`.

The sign flag picks the candidate root or its negation, as decompression does. -/
def decodeBytes : List Nat → Option (Nat × Nat)
  | [] => none
  | h :: t =>
    let x := xOf (h :: t)
    let y := rootCandidate x
    bif Nat.land (h % 256) 0x40 == 0 && fmul y y == rhs x then
      some (x, bif signBit y == (Nat.land (h % 256) 0x20 != 0) then y
        else (Fp.modulus - y) % Fp.modulus)
    else none

/-- The affine point that a list of digit codes encodes. -/
def decodeCodes (ns : List Nat) : Option (Nat × Nat) := (hexBytes ns).bind decodeBytes

/-- The infinity flag reads the same on the byte and on its value mod 256. -/
private theorem flag40_aux :
    ∀ h : Fin 256, ((UInt8.ofNat h.val &&& 0x40) ≠ 0) ↔ Nat.land h.val 0x40 ≠ 0 := by
  decide +kernel

/-- The sign flag reads the same on the byte and on its value mod 256. -/
private theorem flag20_aux :
    ∀ h : Fin 256, ((UInt8.ofNat h.val &&& 0x20) ≠ 0) ↔ Nat.land h.val 0x20 ≠ 0 := by
  decide +kernel

private theorem ofNat_mod (h : Nat) : UInt8.ofNat h = UInt8.ofNat (h % 256) :=
  UInt8.ofNat_mod_size.symm

private theorem flag40 (h : Nat) :
    ((UInt8.ofNat h &&& 0x40) ≠ 0) ↔ Nat.land (h % 256) 0x40 ≠ 0 := by
  rw [ofNat_mod]
  exact flag40_aux ⟨h % 256, Nat.mod_lt _ (by decide)⟩

private theorem flag20 (h : Nat) :
    ((UInt8.ofNat h &&& 0x20) ≠ 0) ↔ Nat.land (h % 256) 0x20 ≠ 0 := by
  rw [ofNat_mod]
  exact flag20_aux ⟨h % 256, Nat.mod_lt _ (by decide)⟩

/-- The choice of decompression does not depend on which root of `y^2` it starts from. -/
private theorem select_eq {y₀ yPos : Fp} (hy : yPos = y₀ ∨ yPos = -y₀) (P : Prop) [Decidable P] :
    (if (Fp.signBit yPos = true) = P then yPos else -yPos) =
      if (Fp.signBit y₀ = true) = P then y₀ else -y₀ := by
  rcases hy with rfl | rfl
  · rfl
  by_cases h0 : y₀ = 0
  · subst h0
    simp
  rw [signBit_neg h0]
  by_cases hP : P <;> cases Fp.signBit y₀ <;> simp [hP]

/-- The value of the negation in `Fp`, as the decoder computes it. -/
private theorem val_neg (y : Fp) : (-y).val = (Fp.modulus - y.val) % Fp.modulus := Fin.val_neg' y

/-- Decompression returns `(x, y, 1)` from the bytes of a string that decodes to `(x, y)`. -/
theorem coords_of_decodeCodes {s : String} {b : ByteArray} {q : G1} {x y : Nat}
    (hd : decodeCodes (codes s) = some (x, y)) (hb : TrustedSetup.hexToBytes? s = some b)
    (hq : G1.uncompress b = .ok q) : coords q = (x, y, 1) := by
  unfold decodeCodes codes at hd
  rw [TrustedSetup.hexToBytes?, SetupTorsion.hexToBytesAux_eq] at hb
  cases hl : hexBytes (s.toList.map Char.toNat) with
  | none => rw [hl] at hd; cases hd
  | some l =>
  rw [hl, Option.bind_some] at hd
  rw [hl, Option.map_some, Option.some.injEq] at hb
  subst hb
  have he : ByteArray.empty.data ++ (l.map UInt8.ofNat).toArray = (l.map UInt8.ofNat).toArray :=
    Array.empty_append
  rw [he] at hq
  cases l with
  | nil => cases hd
  | cons h t =>
  -- The checks of the decoder, and its result.
  simp only [decodeBytes, Bool.cond_eq_ite, Bool.and_eq_true, beq_iff_eq] at hd
  split at hd
  · rename_i hc
    obtain ⟨hinf, hsq⟩ := hc
    cases hd
    -- The branches of decompression.
    have hhead : (⟨((h :: t).map UInt8.ofNat).toArray⟩ : ByteArray).get! 0 = UInt8.ofNat h := rfl
    unfold G1.uncompress at hq
    rw [hhead] at hq
    split at hq
    · cases hq
    dsimp only at hq
    split at hq
    · cases hq
    split at hq
    · rename_i hi
      exact absurd hinf ((flag40 h).mp hi)
    split at hq
    · cases hq
    rename_i xf hx
    split at hq
    · cases hq
    rename_i yPos hsqrt
    cases hq
    have hxv : xf.val = xOf (h :: t) := SetupTorsion.fromBytesBE_eq (by rw [hhead]; exact hx)
    -- Decompression starts from the root of the decoder or from its negation.
    let y₀ : Fp := ⟨rootCandidate (xOf (h :: t)), Nat.mod_lt _ Fp.modulus_pos⟩
    have hy₀ : (y₀ : ZMod Fp.modulus) * y₀ = xf * xf * xf + Fp.ofNat 4 := by
      apply Fin.ext
      rw [Fin.val_mul, Fin.val_add, Fin.val_mul, Fin.val_mul, hxv]
      exact hsq
    have hpm := sqrt_pm ((Fp.sqrt_ok hsqrt).trans hy₀.symm)
    rw [select_eq hpm]
    simp only [coords, hxv]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    -- The sign test of decompression is the sign test of the decoder.
    have hsb : Fp.signBit y₀ = signBit y₀.val := rfl
    have hf := flag20 h
    show (if (Fp.signBit y₀ = true) = _ then y₀ else -y₀).val =
      if signBit y₀.val = (Nat.land (h % 256) 0x20 != 0) then y₀.val
      else (Fp.modulus - y₀.val) % Fp.modulus
    by_cases hs : signBit y₀.val = (Nat.land (h % 256) 0x20 != 0)
    · have hc : (Fp.signBit y₀ = true) = ((UInt8.ofNat h &&& 0x20) ≠ 0) := by
        rw [hsb, hs]
        exact propext ⟨fun h' => hf.mpr (bne_iff_ne.mp h'), fun h' => bne_iff_ne.mpr (hf.mp h')⟩
      rw [ite_eq_left hs, ite_eq_left hc]
    · have hc : ¬ (Fp.signBit y₀ = true) = ((UInt8.ofNat h &&& 0x20) ≠ 0) := by
        intro he
        apply hs
        rw [← hsb]
        exact Bool.eq_iff_iff.mpr (he.to_iff.trans (hf.trans bne_iff_ne.symm))
      rw [ite_eq_right hs, ite_eq_right hc, val_neg]
  · cases hd

/-! ## Points with `z = 1` -/

/-- The point `(x, y, 1)` of `G1`, for naturals `x` and `y`. -/
def affinePoint (x y : Nat) : G1 := ⟨Fp.ofNat x, Fp.ofNat y, Fp.one⟩

/-- The pair is below `p`, and it satisfies the curve equation. -/
def onCurve (x y : Nat) : Bool :=
  Nat.blt x Fp.modulus && Nat.blt y Fp.modulus && fmul y y == rhs x

theorem coords_affinePoint {x y : Nat} (h : onCurve x y = true) :
    coords (affinePoint x y) = (x, y, 1) := by
  simp only [onCurve, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at h
  simp only [coords, affinePoint, Fp.ofNat, Fin.val_ofNat, Nat.mod_eq_of_lt h.1.1,
    Nat.mod_eq_of_lt h.1.2]
  rfl

theorem valid_affinePoint {x y : Nat} (h : onCurve x y = true) : Valid (affinePoint x y) := by
  apply valid_of_affine_eq
  have hc : (Fp.ofNat x).val = x := congrArg (·.1) (coords_affinePoint h)
  have hc' : (Fp.ofNat y).val = y := congrArg (·.2.1) (coords_affinePoint h)
  simp only [onCurve, Bool.and_eq_true, beq_iff_eq] at h
  apply Fin.ext
  show ((Fp.ofNat y) * (Fp.ofNat y)).val = (Fp.ofNat x * Fp.ofNat x * Fp.ofNat x + Fp.ofNat 4).val
  rw [Fin.val_mul, hc', Fin.val_add, Fin.val_mul, Fin.val_mul, hc]
  exact h.2

/-! ## Projective comparison -/

/-- `(X, Y, Z)` with `Z ≠ 0`, `X = x Z^2` and `Y = y Z^3`, mod `p`. -/
def sameAffine (q : Coords) (x y : Nat) : Bool :=
  let z2 := fmul q.2.2 q.2.2
  q.2.2 != 0 && q.1 == fmul x z2 && q.2.1 == fmul y (fmul z2 q.2.2)

/-- A point that the comparison matches with `(x, y)` is the point `(x, y, 1)`. -/
theorem toPoint_eq_of_sameAffine {P Q : G1} {x y : Nat} (hQ : coords Q = (x, y, 1))
    (h : sameAffine (coords P) x y = true) : toPoint P = toPoint Q := by
  simp only [sameAffine, coords, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨hz, hx⟩, hy⟩ := h
  simp only [coords, Prod.mk.injEq] at hQ
  obtain ⟨hqx, hqy, hqz⟩ := hQ
  -- Each coordinate is the cast of its value, and the values are those of the comparison.
  have cast (a : ZMod Fp.modulus) : a = ((a.val : Nat) : ZMod Fp.modulus) :=
    (ZMod.natCast_zmod_val a).symm
  have hzne : rep P 2 ≠ 0 := fun h0 => hz (by rw [show P.z.val = (rep P 2).val from rfl, h0]; rfl)
  have hqz' : rep Q 2 = 1 := by rw [cast (rep Q 2), show (rep Q 2).val = 1 from hqz, Nat.cast_one]
  have hP2 : rep P 2 = (((rep P 2).val : Nat) : ZMod Fp.modulus) := cast _
  refine Point.toAffine_of_equiv (equiv_of_X_eq_of_Y_eq hzne (by rw [hqz']; exact one_ne_zero)
    ?_ ?_)
  · rw [hqz', cast (rep P 0), cast (rep Q 0),
      show (rep P 0).val = x * ((rep P 2).val * (rep P 2).val % Fp.modulus) % Fp.modulus from hx,
      show (rep Q 0).val = x from hqx, hP2]
    simp only [ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id', id]
    ring
  · rw [hqz', cast (rep P 1), cast (rep Q 1),
      show (rep P 1).val = y * ((rep P 2).val * (rep P 2).val % Fp.modulus * (rep P 2).val %
        Fp.modulus) % Fp.modulus from hy,
      show (rep Q 1).val = y from hqy, hP2]
    simp only [ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id', id]
    ring

end EthLib.Cryptography.Kzg.SetupLagrange
