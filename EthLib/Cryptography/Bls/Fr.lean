module

public import EthLib.Cryptography.Bls.Constants
public import EthLib.Cryptography.Bls.Errors
public import EthLib.Cryptography.Montgomery
public import EthLib.Cryptography.Word64.Four
public import EthLib.Cryptography.Hash.Sha256
public import EthLib.Base.ByteOrder
public import EthLib.Base.Bytes

/-!
# `Fr`

The scalar field of BLS12-381, the integers mod the prime group order `r`.

`r = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001`.

An element is held in Montgomery form, as eight limbs of 32 bits, two to a word.

The limbs hold `a R mod r` for the element `a`, with `R = 2 ^ 256`.

So a product needs no division by `r`, and an element reads and writes its bytes directly.

Scalars and base-field elements have distinct types, so they cannot mix by accident.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

protected theorem Fr.modulus_pos : 0 < Fr.modulus := by decide

instance : NeZero Fr.modulus := ⟨by decide⟩

/-- The subgroup order `r` is `|t|^4 - |t|^2 + 1`, for the BLS parameter `t`. -/
theorem Fr.modulus_eq_blsX : Fr.modulus = blsX ^ 4 - blsX ^ 2 + 1 := by decide

/-- The modulus `r` as eight limbs of 32 bits, two to a word, the lowest first. -/
-- Not inline, so that a product reads the words of `r` from memory, as for `Fp`.
@[noinline] def Fr.pLimbs : Montgomery.Limbs.T 8 :=
  ⟨0xffffffff00000001, 0x53bda402fffe5bfe, 0x3339d80809a1d805, 0x73eda753299d7d48⟩

/-- The limbs write the modulus. -/
theorem Fr.val_pLimbs : Montgomery.Limbs.val (n := 8) Fr.pLimbs = modulus := by decide

/-- The four words write the modulus. -/
private theorem Fr.val_raw_pLimbs : Word64.Raw.val Fr.pLimbs = modulus := by
  rw [← Montgomery.Limbs.val_raw]
  exact Fr.val_pLimbs

/-- Twice `r` is below `2^256`, as the products and sums on four words need. -/
private theorem Fr.two_mul_lt : 2 * Word64.Raw.val Fr.pLimbs < 2^256 := by
  rw [Fr.val_raw_pLimbs]
  decide

/-- `-r⁻¹ mod 2 ^ 32`. -/
@[inline] def Fr.pinv : UInt64 := 4294967295

/-- `-r⁻¹ mod 2 ^ 64`. -/
@[inline] def Fr.pinvWord : UInt64 := 0xfffffffeffffffff

/-- An inverse of `2^256` mod `r`, written in two halves of 128 bits. -/
private theorem Fr.radix_inv :
    (0x1bbe869330009d577204078a4f77266a * 2^128 + 0xab6fca8f09dc705f13f75b69fe75c040) *
      2^256 % modulus = 1 := by
  decide +kernel

open Montgomery in
/-- The Montgomery product of the limbs `a` and `b`, on four words of 64 bits. -/
-- The limbs are stored as those words, and both widths have `R = 2 ^ 256`.
def Fr.mulWords (a b : Limbs.T 8) : Limbs.T 8 :=
  Word64.mul4 Fr.pLimbs Fr.pinvWord a b

open Montgomery in
/-- The product on four words is the product on eight limbs, for `a` below `r`. -/
theorem Fr.mulWords_eq (a b : Limbs.T 8) (ha : Limbs.val (n := 8) a < modulus) :
    Fr.mulWords a b =
      Montgomery.mulWords (n := 8) (Limbs.get (n := 8) Fr.pLimbs) Fr.pinv
        (Limbs.get (n := 8) a) (Limbs.get (n := 8) b) Limbs.pack := by
  -- The product on four words, from its spec: below `r`, and `a b 2^(-256)` mod `r`.
  have hpw := Fr.val_raw_pLimbs
  have hpinv : (Word64.Raw.val Fr.pLimbs * Fr.pinvWord.toNat + 1) % 2^64 = 0 := by
    rw [hpw]
    decide +kernel
  have ha' : Word64.Raw.val a < Word64.Raw.val Fr.pLimbs := by
    rw [hpw, ← Limbs.val_raw]; exact ha
  obtain ⟨hl4, he4⟩ := Word64.mul4_spec Fr.two_mul_lt hpinv ha' b
  rw [hpw, ← Limbs.val_raw a, ← Limbs.val_raw b] at he4
  rw [hpw] at hl4
  -- The product on eight limbs, from its spec.
  have hn : num 8 (Limbs.get (n := 8) Fr.pLimbs) 0 = modulus := Fr.val_pLimbs
  obtain ⟨hf, hl, he⟩ := Internal.mulWords_spec (n := 8) (pinv := Fr.pinv)
    (Limbs.fits (n := 8) Fr.pLimbs 0)
    (by rw [hn]; decide) (Limbs.fits (n := 8) a 0) (by rw [hn]; exact ha)
    (Limbs.fits (n := 8) b 0)
  rw [hn] at hl he
  rw [Internal.mulWords_out]
  apply Limbs.val_injective (n := 8)
  rw [Limbs.val_pack hf]
  have e : Limbs.val (n := 8) (Fr.mulWords a b) =
      Word64.Raw.val (Word64.mul4 Fr.pLimbs Fr.pinvWord a b) := by
    rw [Limbs.val_raw, Fr.mulWords]
  refine e.trans ?_
  -- Both are below `r` and agree after a product by `2^256`, so they are equal.
  rw [show 32 * 8 = 256 from rfl] at he
  exact Internal.eq_of_radix_mul_mod Fr.radix_inv hl4 hl (he4.trans he.symm)

open Montgomery in
/-- The sum of the limbs `a` and `b`, reduced once, on four words of 64 bits. -/
@[irreducible] def Fr.addWords (a b : Limbs.T 8) : Limbs.T 8 := Word64.addMod4 Fr.pLimbs a b

open Montgomery in
/-- The sum on four words is the sum on eight limbs, for `a` and `b` below `r`. -/
theorem Fr.addWords_eq (a b : Limbs.T 8) (ha : Limbs.val (n := 8) a < modulus)
    (hb : Limbs.val (n := 8) b < modulus) : Fr.addWords a b = addCore (n := 8) a b Fr.pLimbs := by
  have hp := Fr.val_pLimbs
  apply Limbs.val_injective (n := 8)
  have hs : Limbs.val (n := 8) (Fr.addWords a b) = (Limbs.val a + Limbs.val b) % modulus := by
    rw [Fr.addWords]
    simp only [Limbs.val_raw] at ha hb ⊢
    rw [← Fr.val_raw_pLimbs] at ha hb ⊢
    exact Word64.addMod4_spec Fr.two_mul_lt ha hb
  rw [hs]
  rw [← hp] at ha hb ⊢
  exact (addCore_val ha hb).symm

open Montgomery in
/-- The difference of the limbs `a` and `b`, with `r` added on a borrow, on four words. -/
@[irreducible] def Fr.subWords (a b : Limbs.T 8) : Limbs.T 8 := Word64.subMod4 Fr.pLimbs a b

open Montgomery in
/-- The difference on four words is the difference on eight limbs, for `a` and `b` below `r`. -/
theorem Fr.subWords_eq (a b : Limbs.T 8) (ha : Limbs.val (n := 8) a < modulus)
    (hb : Limbs.val (n := 8) b < modulus) : Fr.subWords a b = subCore (n := 8) a b Fr.pLimbs := by
  have hp := Fr.val_pLimbs
  apply Limbs.val_injective (n := 8)
  have hs : Limbs.val (n := 8) (Fr.subWords a b) =
      (Limbs.val a + modulus - Limbs.val b) % modulus := by
    rw [Fr.subWords]
    simp only [Limbs.val_raw] at ha hb ⊢
    rw [← Fr.val_raw_pLimbs] at ha hb ⊢
    exact Word64.subMod4_spec ha hb
  rw [hs]
  rw [← hp] at ha hb ⊢
  exact (subCore_val ha hb).symm

-- Proofs about `Fr` use the laws of the word arithmetic, never its unfolding on constants.
attribute [irreducible] Fr.mulWords

/-- The modulus `r` with the constants of its Montgomery arithmetic, on eight limbs. -/
-- Inline, so that the compiler sees each field at each use, and the words of `r` from memory.
--
-- The product, the sum and the difference run on four words of 64 bits.
@[inline] def Fr.params : Montgomery.Modulus 8 where
  p := modulus
  pLimbs := Fr.pLimbs
  pinv := Fr.pinv
  r1 := ⟨0x00000001fffffffe, 0x5884b7fa00034802, 0x998c4fefecbc4ff5, 0x1824b159acc5056f⟩
  r2 := ⟨0xc999e990f3f29c6d, 0x2b6cedcb87925c23, 0x05d314967254398f, 0x0748d9d99f59ff11⟩
  pm2 := ⟨0xfffffffeffffffff, 0x53bda402fffe5bfe, 0x3339d80809a1d805, 0x73eda753299d7d48⟩
  pLimbs_spec := Fr.val_pLimbs
  pinv_spec := by decide
  r1_spec := by decide +kernel
  r2_spec := by decide +kernel
  pm2_spec := by decide
  mul := Fr.mulWords
  mul_spec a b ha := Fr.mulWords_eq a b ha
  add := Fr.addWords
  add_spec := Fr.addWords_eq
  sub := Fr.subWords
  sub_spec := Fr.subWords_eq

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

The result pairs the inverses of `xs` with `pre⁻¹`. -/
def batchInverseAux : Fr → List Fr → List Fr × Fr
  -- On the empty list, the result is the empty list and `pre⁻¹`.
  | pre, [] => ([], pre.inverse)
  | pre, x :: xs =>
    -- A zero is skipped and maps to zero, as the inverse maps it.
    if x.isZero then
      let (inverses, s) := batchInverseAux pre xs
      (zero :: inverses, s)
    else
      -- On `x :: t`, the recursion on `t` with `pre * x` gives the inverses of `t`.
      --
      -- It also gives `s = (pre * x)⁻¹`.
      --
      -- Then `x⁻¹ = pre * s` and `pre⁻¹ = s * x`.
      let (inverses, s) := batchInverseAux (pre * x) xs
      (pre * s :: inverses, s * x)

/-- The inverse of every element of `xs`, equal to `xs.map inverse`.

It is Montgomery's simultaneous inversion.

It takes one inversion in total, and three multiplications per element.

One inversion costs about 380 multiplications.

See Montgomery, "Speeding the Pollard and elliptic curve methods of factorization".

It appeared in Mathematics of Computation 48 (1987). -/
def batchInverse (xs : Array Fr) : Array Fr :=
  (batchInverseAux one xs.toList).1.toArray

/-- `a ^ b` raises `a` to `b.val`, treating the exponent as an integer. -/
instance : HPow Fr Fr Fr := ⟨fun a b => powNat a b.val⟩

/-- Decode a 32-byte big-endian integer as an element of `Fr`.

It rejects an integer of at least `r`.

The bytes go straight into limbs, with no integer between. -/
def fromBytesBE (b : Vector UInt8 32) : Except BlsError Fr :=
  -- A vector always has 32 bytes, so this branch is never taken.
  --
  -- The test keeps the kernel from unfolding the limb decoder on bytes it does not know.
  if (Base.packBytes b).size ≠ 32 then .error .nonCanonicalFieldElement
  else
    match Montgomery.ofBytesBE (Base.packBytes b) 0 with
    | some a => .ok a
    | none => .error .nonCanonicalFieldElement

/-- Encode as 32 big-endian bytes. -/
@[inline] def toBytesBE (a : Fr) : ByteArray := Montgomery.toBytesBE a

/-- Hash the data, and convert the digest to an element of `Fr`.

The element is `SHA-256(data) mod r`, with the digest read as a big-endian integer.

The output is not uniform over `Fr`.
-/
def hashToBlsField (data : ByteArray) : Fr :=
  -- The digest `d = SHA-256(data)`.
  let hashedData := Hash.sha256 data
  -- The element is `d mod r`, with the 32 bytes of `d` read as a big-endian integer.
  Fr.ofNat (Base.ByteOrder.ofBE hashedData.data.toList)

end Fr

end EthLib.Cryptography.Bls
