import EthLib.Cryptography.Bls.Compress
import EthLib.Cryptography.Bls.Sha256

/-!
# `HashToCurve`

Hash-to-curve for the BLS12-381 G2 suite
`BLS12381G2_XMD:SHA-256_SSWU_RO_` per RFC 9380.

The pipeline is `expand_message_xmd → hash_to_field → SSWU → 3-isogeny
→ clear_cofactor`. Constants are reproduced verbatim from the RFC.
-/

namespace EthLib.Cryptography.Bls.HashToCurve

open EthLib.Cryptography.Bls

/-! ## `expand_message_xmd` (RFC 9380 §5.3.1) -/

private def sha256BlockSize : Nat := 64
private def sha256OutputSize : Nat := 32
private def oversizeDstPrefix : ByteArray :=
  String.toUTF8 "H2C-OVERSIZE-DST-"

private def i2osp (n : Nat) (len : Nat) : ByteArray :=
  ByteArray.mk <| Array.ofFn (n := len) fun i =>
    UInt8.ofNat ((n >>> ((len - 1 - i.val) * 8)) &&& 0xff)

private def strxor (a b : ByteArray) : ByteArray :=
  ByteArray.mk <| Array.ofFn (n := a.size) fun i => a[i.val]! ^^^ b[i.val]!

/-- Expand `msg` into `lenInBytes` pseudo-random bytes via XMD with
SHA-256. Follows RFC 9380 §5.3.1 and §5.3.3: oversized DSTs are first
shortened with SHA-256, and oversized output requests are rejected. -/
def expandMessageXmd
    (msg : ByteArray) (dst : ByteArray) (lenInBytes : Nat)
    : Except BlsError ByteArray := do
  let ell := (lenInBytes + sha256OutputSize - 1) / sha256OutputSize
  if lenInBytes > 65535 then
    throw (.expandMessageOutputTooLong lenInBytes)
  if ell > 255 then
    throw (.expandMessageTooManyBlocks ell)
  let dst :=
    if dst.size > 255 then
      Sha256.hash (oversizeDstPrefix ++ dst)
    else
      dst
  let zPad := ByteArray.mk (Array.replicate sha256BlockSize 0)
  let dstPrime := dst ++ i2osp dst.size 1
  let lIbStr := i2osp lenInBytes 2
  let msgPrime := zPad ++ msg ++ lIbStr ++ i2osp 0 1 ++ dstPrime
  let b0 := Sha256.hash msgPrime
  let mut bs : Array ByteArray := Array.mkEmpty ell
  let b1 := Sha256.hash (b0 ++ i2osp 1 1 ++ dstPrime)
  bs := bs.push b1
  for i in [2:ell+1] do
    let prev := bs[bs.size - 1]!
    let bi := Sha256.hash (strxor b0 prev ++ i2osp i 1 ++ dstPrime)
    bs := bs.push bi
  let mut out := bs.foldl (· ++ ·) ByteArray.empty
  return out.extract 0 lenInBytes

/-! ## `hash_to_field` for Fp2 (RFC 9380 §5.2)

Returns `count` Fp2 elements, each derived from `2 * L = 128` bytes of
expand-message output. -/

private def fpFromBytesL (b : ByteArray) : Fp :=
  -- OS2IP into a Nat, then reduce mod p.
  let n := Id.run do
    let mut acc : Nat := 0
    for i in [:b.size] do
      acc := (acc <<< 8) ||| b[i]!.toNat
    return acc
  Fp.ofNat n

def hashToFieldFp2
    (msg : ByteArray) (dst : ByteArray) (count : Nat)
    : Except BlsError (Array Fp2) := do
  let l := 64           -- per RFC: ceil((ceil(log2(p)) + k) / 8) = 64 for BLS12-381
  let m := 2
  let lenInBytes := count * m * l
  let uniform ← expandMessageXmd msg dst lenInBytes
  let mut out : Array Fp2 := Array.mkEmpty count
  for i in [:count] do
    let off0 := l * (i * m)
    let off1 := l * (i * m + 1)
    let c0 := fpFromBytesL (uniform.extract off0 (off0 + l))
    let c1 := fpFromBytesL (uniform.extract off1 (off1 + l))
    out := out.push ⟨c0, c1⟩
  return out

/-! ## `sgn0` for Fp / Fp2 (RFC 9380 §4.1) -/

private def sgn0Fp (x : Fp) : Bool := x.val % 2 == 1

private def sgn0Fp2 (x : Fp2) : Bool :=
  let s0 := sgn0Fp x.c0
  let z0 := x.c0.isZero
  let s1 := sgn0Fp x.c1
  s0 || (z0 && s1)

/-! ## SSWU map onto the 3-isogenous curve `E'` (RFC 9380 §6.6.3) -/

/-- `Z = -(2 + I)` for the BLS12-381 G2 suite. -/
private def Z : Fp2 := ⟨-(Fp.ofNat 2), -Fp.one⟩

/-- `A' = 240 * I`. -/
private def Aprime : Fp2 := ⟨Fp.zero, Fp.ofNat 240⟩

/-- `B' = 1012 * (1 + I)`. -/
private def Bprime : Fp2 := ⟨Fp.ofNat 1012, Fp.ofNat 1012⟩

/-- Simplified SWU onto `E' : y^2 = x^3 + A'·x + B'`. -/
private def simpleSwu (u : Fp2) : Fp2 × Fp2 :=
  let u2 := u * u
  let zu2 := Z * u2
  let denom := zu2 * zu2 + zu2          -- Z^2·u^4 + Z·u^2
  let x1 :=
    if denom.isZero then
      -- denom = 0 ⇔ Z·u^2 ∈ {0, -1}; the spec falls back to B'/(Z·A').
      Bprime / (Z * Aprime)
    else
      (-Bprime / Aprime) * (Fp2.one + denom.inverse)
  let gx1 := x1 * x1 * x1 + Aprime * x1 + Bprime
  match Fp2.sqrt gx1 with
  | .ok y =>
    let y := if sgn0Fp2 u = sgn0Fp2 y then y else -y
    (x1, y)
  | .error _ =>
    let x2 := zu2 * x1
    let gx2 := x2 * x2 * x2 + Aprime * x2 + Bprime
    match Fp2.sqrt gx2 with
    | .ok y =>
      let y := if sgn0Fp2 u = sgn0Fp2 y then y else -y
      (x2, y)
    | .error _ => panic! "neither gx1 nor gx2 is a square"

/-! ## 3-isogeny map `E' → E` (RFC 9380 Appendix E.3)

Each `kI_J` is the Fp2 coefficient `k_(I,J)` written as `c0 + c1·I`. -/

private def fp2 (c0 c1 : Nat) : Fp2 := ⟨Fp.ofNat c0, Fp.ofNat c1⟩

-- x_num coefficients
private def k10 : Fp2 := fp2
  0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6
  0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6
private def k11 : Fp2 := fp2
  0
  0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71a
private def k12 : Fp2 := fp2
  0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71e
  0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38d
private def k13 : Fp2 := fp2
  0x171d6541fa38ccfaed6dea691f5fb614cb14b4e7f4e810aa22d6108f142b85757098e38d0f671c7188e2aaaaaaaa5ed1
  0

-- x_den coefficients
private def k20 : Fp2 := fp2
  0
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa63
private def k21 : Fp2 := fp2
  0xc
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa9f

-- y_num coefficients
private def k30 : Fp2 := fp2
  0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706
  0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706
private def k31 : Fp2 := fp2
  0
  0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97be
private def k32 : Fp2 := fp2
  0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71c
  0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38f
private def k33 : Fp2 := fp2
  0x124c9ad43b6cf79bfbf7043de3811ad0761b0f37a1e26286b0e977c69aa274524e79097a56dc4bd9e1b371c71c718b10
  0

-- y_den coefficients
private def k40 : Fp2 := fp2
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb
private def k41 : Fp2 := fp2
  0
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa9d3
private def k42 : Fp2 := fp2
  0x12
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa99

private def isoMapG2 (xp yp : Fp2) : Fp2 × Fp2 :=
  let xp2 := xp * xp
  let xp3 := xp2 * xp
  let xNum := k13 * xp3 + k12 * xp2 + k11 * xp + k10
  let xDen := xp2 + k21 * xp + k20
  let yNum := k33 * xp3 + k32 * xp2 + k31 * xp + k30
  let yDen := xp3 + k42 * xp2 + k41 * xp + k40
  (xNum / xDen, yp * yNum / yDen)

/-! ## Cofactor clearing (RFC 9380 Appendix G.3)

Uses the psi endomorphism for the fast Budroni-Pintore method. -/

/-- Frobenius for `GF(p^2)` with basis `(1, I)`: `c0 + c1·I ↦ c0 − c1·I`. -/
private def frobeniusFp2 (x : Fp2) : Fp2 := ⟨x.c0, -x.c1⟩

/-- `c1_psi = 1 / (1 + I)^((p − 1) / 3)`. -/
private def c1Psi : Fp2 :=
  let oneI : Fp2 := ⟨Fp.one, Fp.one⟩
  (Fp2.powNat oneI ((Fp.modulus - 1) / 3)).inverse

/-- `c2_psi = 1 / (1 + I)^((p − 1) / 2)`. -/
private def c2Psi : Fp2 :=
  let oneI : Fp2 := ⟨Fp.one, Fp.one⟩
  (Fp2.powNat oneI ((Fp.modulus - 1) / 2)).inverse

/-- `c1_psi2 = 1 / 2^((p − 1) / 3)`, lifted into Fp2. -/
private def c1Psi2 : Fp2 :=
  let two : Fp := Fp.ofNat 2
  let v : Fp := (Fp.powNat two ((Fp.modulus - 1) / 3)).inverse
  ⟨v, Fp.zero⟩

private def psi (P : G2) : G2 :=
  if P.z.isZero then P else
    -- Affine form for clarity; G2.add handles re-projection.
    let (x, y) := P.toAffine
    let qx := c1Psi * frobeniusFp2 x
    let qy := c2Psi * frobeniusFp2 y
    ⟨qx, qy, Fp2.one⟩

private def psi2 (P : G2) : G2 :=
  if P.z.isZero then P else
    let (x, y) := P.toAffine
    ⟨c1Psi2 * x, -y, Fp2.one⟩

/-- |x|, the absolute value of the BLS parameter (the actual parameter
is `−|x|`; we negate the result of scalar multiplication where needed). -/
private def blsAbsX : Nat := 0xd201000000010000

/-- Multiply by the negative BLS parameter (`x = −|x|`). -/
private def mulNegX (P : G2) : G2 := G2.neg (G2.mulNat P blsAbsX)

/-- Cofactor clearing for G2 per RFC 9380 G.3. -/
def clearCofactor (P : G2) : G2 :=
  let t1 := mulNegX P
  let t2 := psi P
  let t3 := psi2 (G2.double P)
  let t3 := G2.add t3 (G2.neg t2)
  let t2 := G2.add t1 t2
  let t2 := mulNegX t2
  let t3 := G2.add t3 t2
  let t3 := G2.add t3 (G2.neg t1)
  G2.add t3 (G2.neg P)

/-! ## Top-level pipeline -/

/-- Hash a message + DST to a G2 point on BLS12-381. -/
def hashToG2 (msg : ByteArray) (dst : ByteArray) : Except BlsError G2 := do
  let us ← hashToFieldFp2 msg dst 2
  let (x0, y0) := simpleSwu us[0]!
  let (x1, y1) := simpleSwu us[1]!
  let (xa, ya) := isoMapG2 x0 y0
  let (xb, yb) := isoMapG2 x1 y1
  let p0 : G2 := ⟨xa, ya, Fp2.one⟩
  let p1 : G2 := ⟨xb, yb, Fp2.one⟩
  return clearCofactor (G2.add p0 p1)

end EthLib.Cryptography.Bls.HashToCurve
