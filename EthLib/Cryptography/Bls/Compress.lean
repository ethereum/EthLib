import EthLib.Cryptography.Bls.G1
import EthLib.Cryptography.Bls.G2
import EthLib.Cryptography.Bls.Errors

/-!
# `Compress`

Compressed serialization for G1 and G2, plus `keyValidate`. We follow
[IRTF draft-bls-signature-04 §2.5](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04#section-2.5),
the standard BLS12-381 compressed encoding.

The encoding stuffs three flag bits into the high bits of the first
byte of the x-coordinate:

  bit 7 (0x80) — *compressed*: always 1 here (we don't emit uncompressed)
  bit 6 (0x40) — *infinity*: 1 iff the point is the identity
  bit 5 (0x20) — *y-sign*: 1 iff `y` is the lexicographically larger of
                 the two square roots of `x³ + b`

`keyValidate` decompresses, checks the result is on the curve, checks
subgroup membership by `[r]·P = O`, and rejects the identity point
(per IRTF BLS §2.5). Callers that explicitly *allow* the identity
(e.g. KZG's `validateKzgG1`) wrap `keyValidate` upstream.
-/

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

/-- Square root in `Fp2`. Returns `none` when `a` isn't a square. -/
def Fp2.sqrt (a : Fp2) : Except BlsError Fp2 :=
  -- Pure-imaginary input: handle the case `a1 = 0` directly.
  if a.c1.isZero then
    match Fp.sqrt a.c0 with
    | .ok s => .ok ⟨s, Fp.zero⟩
    | .error _ =>
      -- −a₀ might be a square; if so, `sqrt(a) = 0 + sqrt(−a₀)·i`
      -- because `(s·i)² = s²·(−1) = −s²`.
      match Fp.sqrt (-a.c0) with
      | .ok s    => .ok ⟨Fp.zero, s⟩
      | .error _ => .error .notASquare
  else
    -- Norm = a₀² + a₁² in Fp; we need its sqrt to exist.
    let n := a.c0 * a.c0 + a.c1 * a.c1
    match Fp.sqrt n with
    | .error _ => .error .notASquare
    | .ok s =>
      let twoInv := (Fp.ofNat 2).inverse
      -- Try c₀² = (a₀ + s)/2, then fall back to (a₀ − s)/2.
      let try1 := Fp.sqrt ((a.c0 + s) * twoInv)
      let c0Opt :=
        match try1 with
        | .ok _    => try1
        | .error _ => Fp.sqrt ((a.c0 - s) * twoInv)
      match c0Opt with
      | .error _ => .error .notASquare
      | .ok c0Fp =>
        let c1Fp := a.c1 * (Fp.ofNat 2 * c0Fp).inverse
        .ok ⟨c0Fp, c1Fp⟩

/-- True iff `bytes[start..]` are all zero. -/
private def tailAllZero (bytes : ByteArray) (start : Nat) : Bool := Id.run do
  let mut ok := true
  for i in [start : bytes.size] do
    if bytes.get! i ≠ 0 then ok := false
  return ok

/-! ## G1 -/

namespace G1

/-- Canonical compressed-infinity encoding: `0xc0` then 47 zero bytes. -/
def infinityBytes : ByteArray :=
  ByteArray.mk <| (Array.replicate 48 (0 : UInt8)).set! 0 0xc0

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

/-- Decompress 48 bytes into a `G1` point, failing with `invalidG1Point`
for malformed inputs or non-curve points. -/
def uncompress (bytes : ByteArray) : Except BlsError G1 :=
  if bytes.size ≠ 48 then .error .invalidG1Point
  else
    let head := bytes.get! 0
    let isCompressed := (head &&& 0x80) ≠ 0
    let isInfinity   := (head &&& 0x40) ≠ 0
    let ySign        := (head &&& 0x20) ≠ 0
    if !isCompressed then .error .invalidG1Point
    else if isInfinity then
      -- Infinity must use the canonical encoding `0xc0` + 47 zero bytes
      -- and the y-sign flag must be cleared.
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

/-- Subgroup-membership check via `[r]·P = O`. -/
def inSubgroup (p : G1) : Bool :=
  if p.isInfinity then true else (mulNat p Fr.modulus).isInfinity

/-- Decompress + curve check + subgroup check. Rejects the point at
infinity per the IRTF BLS draft (§2.5); KZG's `validateKzgG1` wraps
this with an explicit infinity-allow. -/
def keyValidate (bytes : ByteArray) : Except BlsError Unit := do
  let p ← uncompress bytes
  if p.isInfinity then throw .pointAtInfinity
  if !inSubgroup p then throw .notInSubgroup

end G1

/-! ## G2 -/

namespace G2

/-- Canonical compressed-infinity encoding: `0xc0` then 95 zero bytes. -/
def infinityBytes : ByteArray :=
  ByteArray.mk <| (Array.replicate 96 (0 : UInt8)).set! 0 0xc0

/-- Encode `Fp2` as 96 big-endian bytes (`c1 ‖ c0`). -/
private def fp2ToBytes (x : Fp2) : ByteArray :=
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

/-- Decompress 96 bytes into a `G2` point, failing with `invalidG2Point`
for malformed inputs or non-curve points. -/
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

/-- Subgroup-membership check via `[r]·P = O`. -/
def inSubgroup (p : G2) : Bool :=
  if p.isInfinity then true else (mulNat p Fr.modulus).isInfinity

end G2

end EthLib.Cryptography.Bls
