module

public import EthLib.Base.BigEndianWords
public import EthLib.Cryptography.Secp256k1.Ecdsa
public import EthLib.Cryptography.Secp256k1.RecoveryMul

/-!
# `Secp256k1.Recovery`

Public key recovery, from SEC 1 v2 §4.1.6.

An Ethereum transaction carries a signature, not a public key.

The key is rebuilt from the signature and the hash, then hashed into the sender's address.

The verification equation `R = u1 G + u2 Q` can be solved for `Q`:

```text
s R = e G + r Q, so Q = r^(-1) (s R - e G)
```

`R` is not sent, but its `x` is `r`, so `R` is one of the two points with that `x`.

The recovery id picks one: `0` for an even `y`, `1` for an odd `y`.

That is the recovery identifier of Appendix F of the Yellow Paper, Shanghai version.

The source is `Paper.tex` at `efc5f9a`:
<https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex>

It declares the ids 2 and 3 invalid.

SEC 1 also tries `x = r + j n` for `j` up to the cofactor `h = 1`, for the rare `x_R >= n`.

Ethereum uses only the ids 0 and 1, so it never tries `x = r + n`, and neither does recovery here.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

namespace Fp.RecoveryField

/-- Repeat a chosen square operation. -/
@[noinline, specialize step] def repeatSquare {F : Type} (step : F → F) : Nat → F → F
  | 0, a => a
  | n + 1, a => repeatSquare step n (step a)

/-- Square an element repeatedly. -/
@[inline] def squareTimes {F : Type} [Mul F] (n : Nat) (a : F) : F :=
  repeatSquare (fun x => x * x) n a

/-- Apply a field step repeatedly with the residue words as separate arguments. -/
@[noinline, specialize step] def repeatWords (step : Element → Element) :
    Nat → (w0 w1 w2 w3 : UInt64) → (Raw.mk w0 w1 w2 w3).val < Fp.modulus → Element
  | 0, w0, w1, w2, w3, h => ⟨⟨w0, w1, w2, w3⟩, h⟩
  | n + 1, w0, w1, w2, w3, h =>
    let a := step ⟨⟨w0, w1, w2, w3⟩, h⟩
    repeatWords step n a.raw.w0 a.raw.w1 a.raw.w2 a.raw.w3 a.lt

/-- Supply the words of the initial value to the field loop. -/
@[inline] def repeatFieldStep (step : Element → Element) (n : Nat) (a : Element) : Element :=
  repeatWords step n a.raw.w0 a.raw.w1 a.raw.w2 a.raw.w3 a.lt

/-- Raise a field element to `(p + 1) / 4` using the three runs of ones in the exponent.

The addition chain uses blocks of 223, 22 and 2 bits as in [libsecp256k1][chain].

[chain]: <https://github.com/bitcoin-core/secp256k1/blob/v0.6.0/src/field_impl.h#L49-L122>
-/
@[inline] def sqrtCandidate (a : Element) : Element :=
  let x2 := repeatFieldStep square 1 a * a
  let x3 := repeatFieldStep square 1 x2 * a
  let x6 := repeatFieldStep square 3 x3 * x3
  let x9 := repeatFieldStep square 3 x6 * x3
  let x11 := repeatFieldStep square 2 x9 * x2
  let x22 := repeatFieldStep square 11 x11 * x11
  let x44 := repeatFieldStep square 22 x22 * x22
  let x88 := repeatFieldStep square 44 x44 * x44
  let x176 := repeatFieldStep square 88 x88 * x88
  let x220 := repeatFieldStep square 44 x176 * x44
  let x223 := repeatFieldStep square 3 x220 * x3
  let x246 := repeatFieldStep square 23 x223 * x22
  let x252 := repeatFieldStep square 6 x246 * x2
  repeatFieldStep square 2 x252

/-- Check the square root while keeping it in the Montgomery representation. -/
@[inline] def sqrtElement (x : Element) : Option Element :=
  let c := sqrtCandidate x
  if square c = x then some c else none

/-- Return the checked square root as a canonical field element. -/
def sqrt (a : Fp) : Option Fp :=
  (sqrtElement (ofFin a)).map toFin

/-- Read the parity of the canonical root from the low word. -/
@[inline] def isOdd (a : Element) : Bool :=
  (a * rawOne).raw.w0 &&& 1 == 1

/-- Select the root in the recovery representation, with the requested parity. -/
@[inline] def selectRoot (x : Element) (root : Option Element) (odd : Bool) :
    Except Secp256k1Error RecoveryMul.Coordinates :=
  match root with
  | none => .error .noPointWithX
  | some y => .ok ⟨x, if isOdd y = odd then y else 0 - y, 1⟩

/-- Reconstruct a point from its X coordinate in the recovery field. -/
@[inline] def decompressField (mx : Element) (odd : Bool) :
    Except Secp256k1Error RecoveryMul.Coordinates :=
  selectRoot mx (sqrtElement (square mx * mx + ofFin b)) odd

/-- Reconstruct the point in the field representation used by the recovery chain. -/
def decompressCoords (x : Fp) (odd : Bool) : Except Secp256k1Error RecoveryMul.Coordinates :=
  decompressField (ofFin x) odd

end Fp.RecoveryField

namespace Ecdsa

/-- Append the 32-byte coordinate in canonical form, in big-endian order. -/
@[inline] def pushCoordinate (out : ByteArray) (x : Fp.RecoveryField.Element) : ByteArray :=
  let raw := (x * Fp.RecoveryField.rawOne).raw
  let out := Base.pushWord64 out raw.w3
  let out := Base.pushWord64 out raw.w2
  let out := Base.pushWord64 out raw.w1
  Base.pushWord64 out raw.w0

/-- Write the affine coordinates in the uncompressed format of SEC 1 v2 §2.3.3. -/
@[inline] def encodeAffine (x y : Fp.RecoveryField.Element) : ByteArray :=
  let out := (ByteArray.emptyWithCapacity 65).push 0x04
  pushCoordinate (pushCoordinate out x) y

/-- Recover the key in projective form, before normalizing its coordinates. -/
@[inline] def recoverProjective (hash : Vector UInt8 32) (r s : Nat) (recoveryId : Fin 2) :
    Except Secp256k1Error RecoveryMul.Coordinates :=
  -- `r` and `s` lie in `[1, n - 1]`, as verification requires.
  if hr : 0 < r ∧ r < Fn.modulus then
    if hs : 0 < s ∧ s < Fn.modulus then
      -- Steps 1.1 to 1.3, with `j = 0`: `R` is the point with `x = r`, since `r < n < p`.
      (Fp.RecoveryField.decompressCoords (Fin.ofNat _ r) (recoveryId == 1)).map fun R =>
        -- Step 1.4 asks `n R = O`, which holds for every point: the cofactor is 1.
        --
        -- Steps 1.5 and 1.6.1: `Q = r^(-1) (s R - e G) = (r^(-1) s) R + (-(r^(-1) e)) G`.
        let e : Fn := Fin.ofNat _ (hashToInt hash)
        let rInv := RecoveryInverse.invFn ⟨r, hr.2⟩
        RecoveryMul.mulProjective (rInv * ⟨s, hs.2⟩) R (-(rInv * e))
    else .error (.scalarOutOfRange s)
  else .error (.scalarOutOfRange r)

/-- Normalize a recovered key and pass its affine coordinates to the caller. -/
@[inline] def finishProjective {A : Type}
    (finish : Fp.RecoveryField.Element → Fp.RecoveryField.Element → A)
    (q : RecoveryMul.Coordinates) : Except Secp256k1Error A :=
  -- A public key is never `O`.
  match q.toAffine RecoveryMul.batchInverse with
  | none => .error .pointAtInfinity
  | some (x, y) => .ok (finish x y)

/-- Return the recovered affine coordinates in a representation chosen by the caller. -/
@[specialize finish] def recoverUsing {A : Type}
    (finish : Fp.RecoveryField.Element → Fp.RecoveryField.Element → A)
    (hash : Vector UInt8 32) (r s : Nat) (recoveryId : Fin 2) : Except Secp256k1Error A :=
  (recoverProjective hash r s recoveryId).bind (finishProjective finish)

/-- The public key whose signature on `hash` is `(r, s)`, by SEC 1 v2 §4.1.6.

The recovery id gives the parity of the `y` of `R`. -/
def recover (hash : Vector UInt8 32) (r s : Nat) (recoveryId : Fin 2) : Except Secp256k1Error Point :=
  -- `r` and `s` lie in `[1, n - 1]`, as verification requires.
  if hr : 0 < r ∧ r < Fn.modulus then
    if hs : 0 < s ∧ s < Fn.modulus then do
      -- Steps 1.1 to 1.3, with `j = 0`: `R` is the point with `x = r`, since `r < n < p`.
      let R ← Point.decompress (Fin.ofNat _ r) (recoveryId == 1)
      -- Step 1.4 asks `n R = O`, which holds for every point: the cofactor is 1.
      -- Steps 1.5 and 1.6.1: `Q = r^(-1) (s R - e G) = (r^(-1) s) R + (-(r^(-1) e)) G`.
      let e : Fn := Fin.ofNat _ (hashToInt hash)
      let rInv := Fn.inv ⟨r, hr.2⟩
      let q := Point.mulAdd (rInv * ⟨s, hs.2⟩) R (-(rInv * e)) .generator
      -- A public key is never `O`.
      if q = .infinity then .error .pointAtInfinity else .ok q
    else .error (.scalarOutOfRange s)
  else .error (.scalarOutOfRange r)

/-- Recover the public key in the SEC 1 uncompressed format. -/
def recoverEncoded (hash : Vector UInt8 32) (r s : Nat) (recoveryId : Fin 2) :
    Except Secp256k1Error ByteArray :=
  recoverUsing encodeAffine hash r s recoveryId
section

open Fp.RecoveryField (Raw rawToNat rawToNat_eq)
open FnRecoveryWords (isZero geOrder)

/-- A signature component must be nonzero and below the group order. -/
@[inline] def invalidSignatureWord (a : Raw) : Bool :=
  isZero a || geOrder a.words

theorem invalidSignatureWord_iff (a : Raw) :
    invalidSignatureWord a = true ↔ ¬ (0 < rawToNat a ∧ rawToNat a < Fn.modulus) := by
  simp only [invalidSignatureWord, Bool.or_eq_true, FnRecoveryWords.isZero_iff,
    FnRecoveryWords.geOrder_iff, rawToNat_eq, ← Raw.val_eq]
  omega

/-- Either out-of-range signature component makes recovery fail. -/
@[inline] def invalidSignatureWords (r s : Raw) : Bool :=
  invalidSignatureWord r || invalidSignatureWord s

theorem invalidSignatureWords_iff (r s : Raw) :
    invalidSignatureWords r s = true ↔
      ¬ ((0 < rawToNat r ∧ rawToNat r < Fn.modulus) ∧
        (0 < rawToNat s ∧ rawToNat s < Fn.modulus)) := by
  simp only [invalidSignatureWords, Bool.or_eq_true, invalidSignatureWord_iff]
  constructor
  · rintro (hr | hs) h
    · exact hr h.1
    · exact hs h.2
  · intro h
    by_cases hr : 0 < rawToNat r ∧ rawToNat r < Fn.modulus
    · exact Or.inr (fun hs => h ⟨hr, hs⟩)
    · exact Or.inl hr

/-- Recover an encoded key directly from the words of the digest and signature. -/
@[inline] def recoverEncodedFromWords (hash r s : Raw) (id : Fin 2) :
    Except Secp256k1Error ByteArray := do
  if h : invalidSignatureWords r s then
    throw (.scalarOutOfRange (rawToNat (if invalidSignatureWord r then r else s)))
  else
    have hr : 0 < rawToNat r ∧ rawToNat r < Fn.modulus :=
      (Decidable.of_not_not (mt (invalidSignatureWords_iff r s).mpr h)).1
    let R ← Fp.RecoveryField.decompressField (Fp.RecoveryField.ofRaw r (by
      rw [← rawToNat_eq]
      exact Nat.lt_trans hr.2 (by decide))) (id == 1)
    let rInv := RecoveryInverse.invFnWords r
    let k := FnRecoveryWords.mul rInv s
    let l := FnRecoveryWords.negate (FnRecoveryWords.mul rInv hash)
    finishProjective encodeAffine (RecoveryMul.mulProjectiveWords k R l)

end

end Ecdsa

end EthLib.Cryptography.Secp256k1
