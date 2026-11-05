module

public import EthLib.Cryptography.Bls.Errors
public import EthLib.Cryptography.Montgomery
public import EthLib.Cryptography.Hash.Sha256

/-!
# `Fr`

The scalar field of BLS12-381, the integers mod the prime group order `r`.

`r = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001`.

An element is held in Montgomery form, as eight limbs of 32 bits.

The limbs hold `a R mod r` for the element `a`, with `R = 2 ^ 256`.

So a product needs no division by `r`, and an element reads and writes its bytes directly.

Scalars and base-field elements have distinct types, so they cannot mix by accident.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

/-- BLS12-381 scalar field modulus (= group order). -/
def Fr.modulus : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

protected theorem Fr.modulus_pos : 0 < Fr.modulus := by decide

instance : NeZero Fr.modulus := ⟨by decide⟩

/-- The modulus `r` with the constants of its Montgomery arithmetic, on eight limbs.

It is inline, so that the compiler sees its fields as constants at each use. -/
@[inline] def Fr.params : Montgomery.Modulus 8 where
  p := modulus
  pLimbs := ⟨1, 4294967295, 4294859774, 1404937218, 161601541, 859428872, 698187080, 1944954707⟩
  pinv := 4294967295
  r1 := ⟨4294967294, 1, 215042, 1485092858, 3971764213, 2576109551, 2898593135, 405057881⟩
  r2 := ⟨4092763245, 3382307216, 2274516003, 728559051, 1918122383, 97719446, 2673475345,
    122214873⟩
  pm2 := ⟨4294967295, 4294967294, 4294859774, 1404937218, 161601541, 859428872, 698187080,
    1944954707⟩
  pLimbs_spec := by decide
  pinv_spec := by decide
  r1_spec := by decide
  r2_spec := by decide
  pm2_spec := by decide

/-- An element of the BLS12-381 scalar field. -/
abbrev Fr := Montgomery Fr.params

namespace Fr

/-- The element that stands for `n mod r`. -/
@[inline] def ofNat (n : Nat) : Fr := Montgomery.ofNat n

/-- The integer below `r` that the element stands for.

Proofs use its lemmas, never its unfolding, which runs a Montgomery reduction. -/
@[inline, irreducible] def val (a : Fr) : Nat := Montgomery.toNat a

@[inline] def zero : Fr := Montgomery.zero
@[inline] def one  : Fr := Montgomery.one

@[inline] def add (a b : Fr) : Fr := a + b
@[inline] def sub (a b : Fr) : Fr := a - b
@[inline] def neg (a : Fr)   : Fr := -a
@[inline] def mul (a b : Fr) : Fr := a * b

@[inline] def beq (a b : Fr) : Bool := a == b
@[inline] def isZero (a : Fr) : Bool := a == zero

/-- Square-and-multiply modular exponentiation. -/
@[inline] def powNat (base : Fr) (e : Nat) : Fr := Montgomery.pow base e

/-- Multiplicative inverse, by Fermat's little theorem: `a ^ (r - 2)`.

The inverse of `0` is `0`, not an error.

A caller must check that the argument is nonzero, or say why it is. -/
@[inline] def inverse (a : Fr) : Fr := Montgomery.inv a

/-- Field division `a * b⁻¹`.

The inverse of `0` is `0`, so a division by zero gives `0`, with no error.

A caller must check that the denominator is nonzero, or say why it is.

-/
instance : Div Fr := ⟨fun a b => a * b.inverse⟩

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

It rejects an input of the wrong size, and an integer of at least `r`.

The bytes go straight into limbs, with no integer between. -/
def fromBytesBE (b : ByteArray) : Except BlsError Fr :=
  if b.size ≠ 32 then .error .nonCanonicalFieldElement
  else
    match Montgomery.ofBytesBE b 0 with
    | some a => .ok a
    | none => .error .nonCanonicalFieldElement

/-- Encode as 32 big-endian bytes. -/
@[inline] def toBytesBE (a : Fr) : ByteArray := Montgomery.toBytesBE a

/-- Hash the data, and convert the digest to an element of `Fr`.

The output is not uniform over `Fr`. -/
def hashToBlsField (data : ByteArray) : Fr :=
  let hashedData := Hash.sha256 data
  Fr.ofNat (bytesBEToNat hashedData)

end Fr

end EthLib.Cryptography.Bls
