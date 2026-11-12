module

public import EthLib.Cryptography.Bls.G1
public import EthLib.Cryptography.Bls.G2
public import EthLib.Cryptography.Bls.Errors

/-!
# `Compress`

The compressed encodings of `G1` and `G2`, and key validation.

They follow §2.5 of the BLS signature draft:
<https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04#section-2.5>

The first byte of the `x` coordinate carries three flags in its top bits.

- Bit 7, `0x80`, marks a compressed point, and it is always set here.
- Bit 6, `0x40`, marks the point at infinity.
- Bit 5, `0x20`, is set when `y` is the larger of the two square roots of `x^3 + b`.

Key validation decompresses the point, and checks that it is on the curve.

It then checks that `[r] P = O`, and rejects the point at infinity.

KZG accepts the point at infinity, so it tests for that encoding before key validation.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

/-! ## Sign convention -/

/-- True iff `y > p − y`, the "lex-larger" half. -/
@[inline] def Fp.signBit (y : Fp) : Bool :=
  y.val > Fp.modulus - y.val

/-- Lex-order sign on `Fp2`: compare `c1` first, then `c0`. -/
def Fp2.signBit (y : Fp2) : Bool :=
  if !y.c1.isZero then
    Fp.signBit y.c1
  else
    Fp.signBit y.c0

/-! ## Square root in Fp2 -/

section Sqrt

variable {F : Type} [BaseField F]

/-- A square root in `Fp2`, by the [complex method][source] of Adj and Rodríguez-Henríquez, §V.A.

It relies on the base-field candidate, whose square is its input or the negation of its input.

Over `Fp`, it fails with the error for a non-square exactly when the input has no root.

Which of the two roots it returns is not fixed, since every caller chooses the sign afterwards.

Write the input as `a0 + a1*i` with `i^2 = -1`, and let `s` be a root of the norm `a0^2 + a1^2`.

The base-field candidate `c` of `(a0 + s)/2` squares to it or to its negation.

In the first case `c + (a1/(2*c))*i` is a root, and in the second `a1/(2*c) + c*i` is one.

So over `Fp`, a real input needs one exponentiation, and any other input at most two.

[source]: https://eprint.iacr.org/2012/685
-/
def Fp2.sqrt (a : Fp2 F) : Except BlsError (Fp2 F) :=
  -- Real input: the candidate of `a0` squares to `a0` or to `-a0`.
  if BaseField.isZero a.c1 then
    let c := BaseField.sqrtCandidate a.c0
    if BaseField.beq (c * c) a.c0 then .ok ⟨c, BaseField.zero⟩
    else .ok ⟨BaseField.zero, c⟩
  else
    match sqrtOrError (a.c0 * a.c0 + a.c1 * a.c1) with
    | .error _ => .error .notASquare
    | .ok s =>
      let u := (a.c0 + s) * BaseField.inverse (BaseField.ofNat 2 : F)
      let c := BaseField.sqrtCandidate u
      let d := a.c1 * BaseField.inverse (BaseField.ofNat 2 * c)
      if BaseField.beq (c * c) u then .ok ⟨c, d⟩ else .ok ⟨d, c⟩

end Sqrt

/-- True iff `bytes[start..]` are all zero. -/
-- The exposed decoders need this body for downstream reduction.
--
-- The check recurses on the number of tail bytes, so the kernel reduces it on a literal encoding.
--
-- Compiled, it is a loop over the bytes in place that stops at the first nonzero byte.
def tailAllZero (bytes : ByteArray) (start : Nat) : Bool :=
  (bytes.size - start).all fun i h => bytes[start + i]'(by omega) == 0

/-! ## G1 -/

/-- An `Fp` element encodes as 48 bytes. -/
theorem Fp.size_toBytesBE (x : Fp) : (Fp.toBytesBE x).size = 48 :=
  Montgomery.toBytesBE_size x

private theorem size_set! (b : ByteArray) (j : Nat) (v : UInt8) : (b.set! j v).size = b.size :=
  Array.size_setIfInBounds

namespace G1

/-- Canonical compressed-infinity encoding: `0xc0` then 47 zero bytes. -/
def infinityBytes : ByteArray :=
  ByteArray.mk ((Vector.replicate 48 (0 : UInt8)).set 0 0xc0).toArray

/-- Compressed 48-byte serialization. -/
def compress (p : G1) : ByteArray := Id.run do
  if p.isInfinity then return infinityBytes
  let (x, y) := p.toAffine
  -- 48 big-endian bytes for `x`. We then OR the flag bits into byte 0.
  let xBytes := x.toBytesBE
  let mut bytes := xBytes.set! 0 ((xBytes.get! 0) ||| 0x80)
  if Fp.signBit y then
    bytes := bytes.set! 0 ((bytes.get! 0) ||| 0x20)
  return bytes

/-- Decompress 48 bytes into a point of `G1`.

It fails on a malformed input and on a point off the curve. -/
def uncompress (bytes : ByteArray) : Except BlsError G1 :=
  if bytes.size ≠ 48 then .error .invalidG1Point
  else
    let head := bytes.get! 0
    let isCompressed := (head &&& 0x80) ≠ 0
    let isInfinity   := (head &&& 0x40) ≠ 0
    let ySign        := (head &&& 0x20) ≠ 0
    if !isCompressed then .error .invalidG1Point
    else if isInfinity then
      -- Infinity must be the canonical encoding, `0xc0` then 47 zero bytes, with no sign flag.
      if ySign || head ≠ 0xc0 || !tailAllZero bytes 1 then .error .invalidG1Point
      else .ok G1.zero
    else
      -- Strip flag bits from the high byte before decoding `x`.
      let xBytes := bytes.set! 0 (head &&& 0x1f)
      match Fp.fromBytesBE xBytes with
      | .error _ => .error .invalidG1Point
      | .ok x =>
        -- Compute y² = x³ + 4 and take a sqrt.
        let rhs := x * x * x + Fp.ofNat 4
        match Fp.sqrt rhs with
        | .error _ => .error .invalidG1Point
        | .ok yPos =>
          let y := if Fp.signBit yPos = ySign then yPos else -yPos
          .ok ⟨x, y, Fp.one⟩

/-- A compressed `G1` point has 48 bytes. -/
theorem size_compress (p : G1) : (compress p).size = 48 := by
  unfold compress
  simp only [Id.run]
  split
  · rfl
  · split
    · exact (size_set! ..).trans ((size_set! ..).trans (Fp.size_toBytesBE _))
    · exact (size_set! ..).trans (Fp.size_toBytesBE _)

/-- Subgroup-membership check by the endomorphism `σ(x, y) = (β x, y)`.

A point passes when `σ(P) = [-t^2] P`, where `t` is the BLS parameter.

The test is the one of Scott for `G1`, <https://eprint.iacr.org/2021/1130>.

For a point on the curve, the proofs show that it holds exactly when `[r] P = O`.

`[t^2]` is two products by the 64-bit `|t|`, so the test takes about 128 doublings. -/
def inSubgroup (p : G1) : Bool :=
  if p.isInfinity then true
  else projectiveEq (sigma p) (neg (mulNat (mulNat p blsX) blsX))

/-- Validate a compressed public key and return its point.

The checks are those of `KeyValidate` in the IRTF BLS signature draft, section 2.5:

1. The bytes decompress to a point on the curve.
2. The point is not the point at infinity.
3. The point lies in the subgroup of prime order `r`.

KZG accepts the point at infinity, so it tests for that encoding before calling this.
-/
def keyValidatePoint (bytes : ByteArray) : Except BlsError G1 := do
  -- Reject bytes that do not encode a point on the curve.
  let p ← uncompress bytes
  -- The identity is on the curve, but it is never a valid public key.
  if p.isInfinity then throw .pointAtInfinity
  -- A point outside the order-r subgroup would open small-subgroup attacks.
  if !inSubgroup p then throw .notInSubgroup
  return p

/-- Validate a compressed public key, by key validation of the BLS signature draft, §2.5.

This runs the same checks as the point-returning version and discards the point.
-/
def keyValidate (bytes : ByteArray) : Except BlsError Unit := do
  let _ ← keyValidatePoint bytes

end G1

/-! ## G2 -/

namespace G2

/-- Canonical compressed-infinity encoding: `0xc0` then 95 zero bytes. -/
def infinityBytes : ByteArray :=
  ByteArray.mk ((Vector.replicate 96 (0 : UInt8)).set 0 0xc0).toArray

/-- Encode `Fp2` as 96 big-endian bytes (`c1 ‖ c0`). -/
def fp2ToBytes (x : Fp2) : ByteArray :=
  x.c1.toBytesBE ++ x.c0.toBytesBE

/-- Compressed 96-byte serialization. -/
def compress (p : G2) : ByteArray := Id.run do
  if p.isInfinity then return infinityBytes
  let (x, y) := p.toAffine
  let xBytes := fp2ToBytes x
  let mut bytes := xBytes.set! 0 ((xBytes.get! 0) ||| 0x80)
  if Fp2.signBit y then
    bytes := bytes.set! 0 ((bytes.get! 0) ||| 0x20)
  return bytes

/-- An `Fp2` element encodes as `c1` then `c0`, `48 + 48 = 96` bytes. -/
@[simp] theorem size_fp2ToBytes (x : Fp2) : (fp2ToBytes x).size = 96 := by
  rw [fp2ToBytes, ByteArray.size_append, Fp.size_toBytesBE, Fp.size_toBytesBE]

/-- A compressed `G2` point has 96 bytes. -/
theorem size_compress (p : G2) : (compress p).size = 96 := by
  rcases hpa : p.toAffine with ⟨xa, ya⟩
  by_cases h : p.isInfinity = true
  · have he : compress p = infinityBytes := by
      unfold compress
      simp only [Id.run, h, ↓reduceIte]
      rfl
    rw [he]
    rfl
  · have he : compress p =
        (let base := (fp2ToBytes xa).set! 0 ((fp2ToBytes xa).get! 0 ||| 0x80)
         if Fp2.signBit ya then base.set! 0 (base.get! 0 ||| 0x20) else base) := by
      unfold compress
      simp only [Id.run, h, hpa]
      rfl
    rw [he]
    dsimp only
    split <;> simp only [size_set!, size_fp2ToBytes]

/-- Decompress 96 bytes into a point of `G2`.

It fails on a malformed input and on a point off the curve. -/
def uncompress (bytes : ByteArray) : Except BlsError G2 :=
  if bytes.size ≠ 96 then .error .invalidG2Point
  else
    let head := bytes.get! 0
    let isCompressed := (head &&& 0x80) ≠ 0
    let isInfinity   := (head &&& 0x40) ≠ 0
    let ySign        := (head &&& 0x20) ≠ 0
    if !isCompressed then .error .invalidG2Point
    else if isInfinity then
      if ySign || head ≠ 0xc0 || !tailAllZero bytes 1 then .error .invalidG2Point
      else .ok G2.zero
    else
      let cleared := bytes.set! 0 (head &&& 0x1f)
      let c1Bytes := cleared.extract 0 48
      let c0Bytes := cleared.extract 48 96
      match Fp.fromBytesBE c1Bytes, Fp.fromBytesBE c0Bytes with
      | .ok c1, .ok c0 =>
        let x : Fp2 := ⟨c0, c1⟩
        let rhs := x * x * x + bTwist
        match Fp2.sqrt rhs with
        | .error _ => .error .invalidG2Point
        | .ok yPos =>
          let yNeg := -yPos
          let y := if Fp2.signBit yPos = ySign then yPos else yNeg
          .ok ⟨x, y, Fp2.one⟩
      | _, _ => .error .invalidG2Point

/-- Subgroup-membership check by the endomorphism `psi` of the twist.

A point passes when `psi(P) = [t] P`, where `t` is the BLS parameter.

The test is the one of Scott for `G2`, <https://eprint.iacr.org/2021/1130>.

For a point on the twist, the proofs show that it holds exactly when `[r] P = O`.

`t` is negative, so `[t] P` is `-[|t|] P`, one product by the 64-bit `|t|`. -/
def inSubgroup (p : G2) : Bool :=
  if p.isInfinity then true
  else projectiveEq (psi p) (neg (mulNat p blsX))

end G2

end EthLib.Cryptography.Bls
