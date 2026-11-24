module

public import EthLib.Base.Bytes
public import EthLib.Cryptography.Bls.G1
public import EthLib.Cryptography.Bls.G2
public import EthLib.Cryptography.Bls.Errors

/-!
# `Compress`

The compressed encodings of `G1` and `G2`, and key validation.

The BLS signature draft takes the compressed encodings of ZCash, in its Appendix A:
<https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04#appendix-A>

Key validation follows its §2.5:
<https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04#section-2.5>

The step comments of the encodings follow Appendix C of the pairing-friendly curves draft:
<https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-pairing-friendly-curves-11#appendix-C>
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

open EthLib.Base (packBytes)

/-! ## Sign convention -/

/-- True iff `y > p − y`, so `y` is the larger of `y` and `-y` as integers below `p`. -/
@[inline] def Fp.signBit (y : Fp) : Bool :=
  -- `sign_GF_p(y) = 1` iff `y > (p - 1) / 2`, which is `y > p - y` for an odd `p`.
  y.val > Fp.modulus - y.val

/-- Lex-order sign on `Fp2`: compare `c1` first, then `c0`. -/
def Fp2.signBit (y : Fp2) : Bool :=
  -- `sign_GF_p^2(y') = sign_GF_p(y'_1)` if `y'_1 ≠ 0`, and `sign_GF_p(y'_0)` otherwise.
  if !y.c1.isZero then
    Fp.signBit y.c1
  else
    Fp.signBit y.c0

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

namespace G1

/-- Canonical compressed-infinity encoding: `0xc0` then 47 zero bytes. -/
def infinityBytes : Vector UInt8 48 :=
  (Vector.replicate 48 (0 : UInt8)).set 0 0xc0

/-- Compressed 48-byte serialization. -/
def compress (p : G1) : Vector UInt8 48 := Id.run do
  -- C.1 steps 1 to 7 at infinity: `m_byte = 0xc0` and `x_string = I2OSP(0, 48)`.
  if p.isInfinity then return infinityBytes
  let (x, y) := p.toAffine
  -- Step 3: `x_string = I2OSP(x, 48)`; step 4 leaves `y_string` empty.
  let xBytes : Vector UInt8 48 := ⟨x.toBytesBE.data, Fp.size_toBytesBE x⟩
  -- Steps 1, 2 and 6: `s_string[0] = x_string[0] OR m_byte`, with `C_bit = 1`, `I_bit = 0`.
  let mut bytes := xBytes.set 0 (xBytes[0] ||| 0x80)
  -- Step 1: `S_bit = sign_GF_p(y)`.
  if Fp.signBit y then
    bytes := bytes.set 0 (bytes[0] ||| 0x20)
  return bytes

/-- Decompress 48 bytes into a point of `G1`.

It fails on a malformed input and on a point off the curve. -/
def uncompress (bytes : Vector UInt8 48) : Except BlsError G1 :=
  -- C.2 step 1: `C_bit`, `I_bit` and `S_bit` are the top three bits of `s_string[0]`.
  --
  -- They mark the compressed form, the point at infinity, and the sign of `y`.
  --
  -- `S_bit` marks the larger square root `y` of `x^3 + b`.
  --
  -- Only the compressed form is read or written here, so `C_bit` is always set.
  let head := bytes[0]
  let isCompressed := (head &&& 0x80) ≠ 0
  let isInfinity   := (head &&& 0x40) ≠ 0
  let ySign        := (head &&& 0x20) ≠ 0
  -- Step 2: with `C_bit = 0`, a point of `E` has 96 bytes, so 48 bytes are INVALID.
  if !isCompressed then .error .invalidG1Point
  else if isInfinity then
    -- Steps 1, 3 and 4: `m_byte = 0xE0` is INVALID, and the other bits must all be zero.
    if ySign || head ≠ 0xc0 || !tailAllZero (packBytes bytes) 1 then .error .invalidG1Point
    else .ok G1.zero
  else
    -- Step 3: `s_string[0] = s_string[0] AND 0x1F`.
    let xBytes := bytes.set 0 (head &&& 0x1f)
    -- Step 6: `x = OS2IP(s_string)`.
    --
    -- Not in Appendix C: `x >= p` is INVALID, since step 3 of C.1 never writes it.
    --
    -- The BLS draft, §2.2, rejects any string that serialization does not output.
    match Fp.fromBytesBE (packBytes xBytes) with
    | .error _ => .error .invalidG1Point
    | .ok x =>
      -- Step 7: `y2 = x^3 + 4`; INVALID if `y2` is not a square, else `y = sqrt(y2)`.
      let rhs := x * x * x + Fp.ofNat 4
      match Fp.sqrt rhs with
      | .error _ => .error .invalidG1Point
      | .ok yPos =>
        -- Step 8: `P = (x, y)` if `S_bit` equals `Y_bit = sign_GF_p(y)`, else `P = (x, -y)`.
        let y := if Fp.signBit yPos = ySign then yPos else -yPos
        .ok ⟨x, y, Fp.one⟩

/-- Subgroup-membership check by the endomorphism `σ(x, y) = (β x, y)`.

A point passes when `σ(P) = [-t^2] P`, where `t` is the BLS parameter.

The test is the one of Scott for `G1`, <https://eprint.iacr.org/2021/1130>.

For a point on the curve, the proofs show that it holds exactly when `[r] P = O`.

`[t^2]` is two products by the 64-bit `|t|`, so the test takes about 128 doublings. -/
def inSubgroup (p : G1) : Bool :=
  -- The subgroup check of `G1`: `O` lies in every subgroup.
  if p.isInfinity then true
  else projectiveEq (sigma p) (neg (mulNat (mulNat p blsX) blsX))

/-- Validate a compressed public key and return its point (BLS signature draft, §2.5).

KZG accepts the point at infinity, so it tests for that encoding before calling this.
-/
def keyValidatePoint (bytes : Vector UInt8 48) : Except BlsError G1 := do
  -- Steps 1 and 2: `xP` is the point that `PK` encodes, or INVALID.
  let p ← uncompress bytes
  -- Step 3: INVALID if `xP` is the identity element, which is on the curve.
  if p.isInfinity then throw .pointAtInfinity
  -- Step 4: INVALID unless `xP` is in `G1`, against small-subgroup attacks.
  if !inSubgroup p then throw .notInSubgroup
  -- Step 5: VALID.
  return p

/-- Validate a compressed public key, by key validation of the BLS signature draft, §2.5.

This runs the same checks as the point-returning version and discards the point.
-/
def keyValidate (bytes : Vector UInt8 48) : Except BlsError Unit := do
  let _ ← keyValidatePoint bytes

end G1

/-! ## G2 -/

namespace G2

/-- Canonical compressed-infinity encoding: `0xc0` then 95 zero bytes. -/
def infinityBytes : Vector UInt8 96 :=
  (Vector.replicate 96 (0 : UInt8)).set 0 0xc0

/-- Encode `Fp2` as 96 big-endian bytes (`c1 ‖ c0`). -/
def fp2ToBytes (x : Fp2) : ByteArray :=
  -- C.1 step 3 on `E'`: `x_string = I2OSP(x_1, 48) || I2OSP(x_0, 48)`.
  x.c1.toBytesBE ++ x.c0.toBytesBE

/-- An `Fp2` element encodes as `c1` then `c0`, `48 + 48 = 96` bytes. -/
@[simp] theorem size_fp2ToBytes (x : Fp2) : (fp2ToBytes x).size = 96 := by
  rw [fp2ToBytes, ByteArray.size_append, Fp.size_toBytesBE, Fp.size_toBytesBE]

/-- Compressed 96-byte serialization. -/
def compress (p : G2) : Vector UInt8 96 := Id.run do
  -- C.1 steps 1 to 7 at infinity: `m_byte = 0xc0` and `x_string = I2OSP(0, 96)`.
  if p.isInfinity then return infinityBytes
  let (x, y) := p.toAffine
  -- Step 3: `x_string = I2OSP(x_1, 48) || I2OSP(x_0, 48)`; step 4 leaves `y_string` empty.
  let xBytes : Vector UInt8 96 := ⟨(fp2ToBytes x).data, size_fp2ToBytes x⟩
  -- Steps 1, 2 and 6: `s_string[0] = x_string[0] OR m_byte`, with `C_bit = 1`, `I_bit = 0`.
  let mut bytes := xBytes.set 0 (xBytes[0] ||| 0x80)
  -- Step 1: `S_bit = sign_GF_p^2(y)`.
  if Fp2.signBit y then
    bytes := bytes.set 0 (bytes[0] ||| 0x20)
  return bytes

/-- Decompress 96 bytes into a point of `G2`.

It fails on a malformed input and on a point off the curve. -/
def uncompress (bytes : Vector UInt8 96) : Except BlsError G2 :=
  -- C.2 step 1: `C_bit`, `I_bit` and `S_bit` are the top three bits of `s_string[0]`.
  --
  -- They mark the compressed form, the point at infinity, and the sign of `y`.
  --
  -- `S_bit` marks the larger square root `y` of `x^3 + b`.
  --
  -- Only the compressed form is read or written here, so `C_bit` is always set.
  let head := bytes[0]
  let isCompressed := (head &&& 0x80) ≠ 0
  let isInfinity   := (head &&& 0x40) ≠ 0
  let ySign        := (head &&& 0x20) ≠ 0
  -- Step 2: with `C_bit = 0`, 96 bytes are a point of `E`, not of `E'`: INVALID here.
  if !isCompressed then .error .invalidG2Point
  else if isInfinity then
    -- Steps 1, 3 and 4: `m_byte = 0xE0` is INVALID, and the other bits must all be zero.
    if ySign || head ≠ 0xc0 || !tailAllZero (packBytes bytes) 1 then .error .invalidG2Point
    else .ok G2.zero
  else
    -- Step 3: `s_string[0] = s_string[0] AND 0x1F`.
    let cleared := packBytes (bytes.set 0 (head &&& 0x1f))
    -- Step 6: `x = x_0 + x_1 u`, from the halves that step 3 of C.1 writes, `x_1` first.
    --
    -- Not in Appendix C: `x_0 ≥ p` or `x_1 ≥ p` is INVALID, since step 3 of C.1 never writes it.
    --
    -- The BLS draft, §2.2, rejects any string that serialization does not output.
    let c1Bytes := cleared.extract 0 48
    let c0Bytes := cleared.extract 48 96
    match Fp.fromBytesBE c1Bytes, Fp.fromBytesBE c0Bytes with
    | .ok c1, .ok c0 =>
      let x : Fp2 := ⟨c0, c1⟩
      -- Step 7: `y2 = x^3 + 4 * (u + 1)`; INVALID if `y2` is not a square, else `y = sqrt(y2)`.
      let rhs := x * x * x + bTwist
      match Fp2.sqrt rhs with
      | none => .error .invalidG2Point
      | some yPos =>
        -- Step 8: `P = (x, y)` if `S_bit` equals `Y_bit = sign_GF_p^2(y)`, else `P = (x, -y)`.
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
  -- The subgroup check of `G2`: `O` lies in every subgroup.
  if p.isInfinity then true
  else (psi p).projectiveEq (neg (p.mulNat blsX))

end G2

end EthLib.Cryptography.Bls
