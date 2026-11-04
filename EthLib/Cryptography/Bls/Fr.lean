module

public import EthLib.Cryptography.Bls.Errors
public import EthLib.Cryptography.Hash.Sha256

/-!
# `Fr`

The scalar field of BLS12-381, the integers mod the prime group order `r`.

`r = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001`.

`Fr` is `Fin r`, so every element is below `r` by construction.

Scalars and base-field elements have distinct types, so they cannot mix by accident.

Core gives `Fin` its `+`, `-`, `*` and negation, all reduced mod `r`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

/-- BLS12-381 scalar field modulus (= group order). -/
def Fr.modulus : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

protected theorem Fr.modulus_pos : 0 < Fr.modulus := by decide

instance : NeZero Fr.modulus := ⟨by decide⟩

/-- An element of the BLS12-381 scalar field. -/
abbrev Fr := Fin Fr.modulus

namespace Fr

@[inline] def ofNat (n : Nat) : Fr := Fin.ofNat modulus n

@[inline] def zero : Fr := ⟨0, Fr.modulus_pos⟩
@[inline] def one  : Fr := ⟨1, by decide⟩

@[inline] def add (a b : Fr) : Fr := a + b
@[inline] def sub (a b : Fr) : Fr := a - b
@[inline] def neg (a : Fr)   : Fr := -a
@[inline] def mul (a b : Fr) : Fr := a * b

@[inline] def beq (a b : Fr) : Bool := a.val == b.val
@[inline] def isZero (a : Fr) : Bool := a.val == 0

/-- Square-and-multiply modular exponentiation. -/
def powNat (base : Fr) (e : Nat) : Fr :=
  if e = 0 then one
  else
    let half := powNat (base * base) (e / 2)
    if e % 2 = 1 then base * half else half
termination_by e
decreasing_by omega

/-- Multiplicative inverse by Fermat's little theorem: `a^(r - 2)`.

So the inverse of `0` is `0`, not an error.

A caller must check that the argument is nonzero, or say why it is. -/
@[inline] def inverse (a : Fr) : Fr := powNat a (modulus - 2)

/-- Field division `a * b⁻¹`.

The inverse of `0` is `0`, so a division by zero gives `0`, with no error.

A caller must check that the denominator is nonzero, or say why it is.

Core already has a division on `Fin n`, which divides the integers.

That division is wrong for a field element, so this instance has high priority. -/
instance (priority := high) : Div Fr := ⟨fun a b => a * b.inverse⟩

/-- The inverses of `xs`, from a single inversion.

`pre` is the product of the nonzero elements before `xs`.

The result pairs the inverses of `xs` with `pre⁻¹`.

On the empty list, the result is the empty list and `pre⁻¹`.

On `x :: t`, the recursion on `t` with `pre * x` gives the inverses of `t` and `s = (pre * x)⁻¹`.

Then `x⁻¹ = pre * s` and `pre⁻¹ = s * x`.

A zero is skipped and maps to zero, as `inverse` maps it. -/
def batchInverseAux : Fr → List Fr → List Fr × Fr
  | pre, [] => ([], pre.inverse)
  | pre, x :: xs =>
    if x.isZero then
      let (inverses, s) := batchInverseAux pre xs
      (zero :: inverses, s)
    else
      let (inverses, s) := batchInverseAux (pre * x) xs
      (pre * s :: inverses, s * x)

/-- The inverse of every element of `xs`, equal to `xs.map inverse`.

It is Montgomery's simultaneous inversion.

One inversion costs about 380 multiplications.

This takes one inversion in total, and three multiplications per element.

See Montgomery, "Speeding the Pollard and elliptic curve methods of factorization".

It appeared in Mathematics of Computation 48 (1987). -/
def batchInverse (xs : Array Fr) : Array Fr :=
  (batchInverseAux one xs.toList).1.toArray

/-- `a ^ b` raises `a` to `b.val`, treating the exponent as an integer. -/
instance : HPow Fr Fr Fr := ⟨fun a b => powNat a b.val⟩

/-- Big-endian accumulation of `bytes` onto `acc`. -/
def fromBytesBEAux (acc : Nat) : List UInt8 → Nat
  | [] => acc
  | b :: rest => fromBytesBEAux ((acc <<< 8) ||| b.toNat) rest

/-- Decode big-endian bytes as a natural number.

Both decoders of field elements from bytes use it. -/
@[inline] def bytesBEToNat (b : ByteArray) : Nat :=
  fromBytesBEAux 0 b.data.toList

/-- Decode a 32-byte big-endian integer as an element of `Fr`.

It rejects an input of the wrong size, and an integer of at least `r`. -/
def fromBytesBE (b : ByteArray) : Except BlsError Fr :=
  if b.size ≠ 32 then .error .nonCanonicalFieldElement
  else
    let acc := bytesBEToNat b
    if h : acc < modulus then .ok ⟨acc, h⟩ else .error .nonCanonicalFieldElement

/-- Encode as 32 big-endian bytes. -/
def toBytesBE (a : Fr) : ByteArray :=
  ByteArray.mk <| Array.ofFn (n := 32) fun i =>
    UInt8.ofNat ((a.val >>> ((31 - i.val) * 8)) &&& 0xff)

/-- Hash the data, and convert the digest to an element of `Fr`.

The output is not uniform over `Fr`. -/
def hashToBlsField (data : ByteArray) : Fr :=
  let hashedData := Hash.sha256 data
  Fr.ofNat (bytesBEToNat hashedData)

end Fr

end EthLib.Cryptography.Bls
