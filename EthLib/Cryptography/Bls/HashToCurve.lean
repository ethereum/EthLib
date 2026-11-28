module

public import EthLib.Cryptography.Bls.G2
public import EthLib.Cryptography.Bls.Errors
public import EthLib.Cryptography.Hash.Sha256
public import EthLib.Base.ByteOrder

/-!
# `HashToCurve`

The hash to `G2` of the suite `BLS12381G2_XMD:SHA-256_SSWU_RO_` of RFC 9380.

The steps are the message expansion, the hash to the field, the SSWU map and the 3-isogeny.

The cofactor clearing ends it.

The constants are those of the RFC.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.HashToCurve

variable {F : Type} [BaseField F]

open EthLib.Cryptography.Bls

/-! ## Message expansion (RFC 9380 §5.3.1)

The message expansion of [RFC 9380 §5.3.1][xmd], with SHA-256 as the hash `H`.

[xmd]: https://www.rfc-editor.org/rfc/rfc9380#section-5.3.1
-/


/-- The 17 ASCII bytes `H2C-OVERSIZE-DST-` of [RFC 9380 §5.3.3][long].

`DST_prime` writes the length of the tag in one byte, so a tag has at most 255 bytes.

A longer tag is replaced by the SHA-256 digest of this prefix followed by the tag.

[long]: https://www.rfc-editor.org/rfc/rfc9380#section-5.3.3
-/
def oversizeDstPrefix : ByteArray :=
  String.toUTF8 "H2C-OVERSIZE-DST-"

/-- `I2OSP(n, len)` of [RFC 8017 §4.1][i2osp]: `n` as `len` bytes, the most significant first.

[RFC 9380 §4][utils] takes it from RFC 8017.

For example, `I2OSP(258, 2)` is the two bytes `0x01 0x02`.

RFC 8017 rejects `n >= 256^len`, and this function keeps the low `len` bytes of `n` instead.

Every caller passes `n < 256^len`, so the two agree:

- A tag length is at most 255, written in one byte.
- An output length is at most 65535, written in two bytes.
- A block index is at most 255, written in one byte.
- Key generation writes 0 in one byte, and its output length 48 in two bytes.

[i2osp]: https://www.rfc-editor.org/rfc/rfc8017#section-4.1
[utils]: https://www.rfc-editor.org/rfc/rfc9380#section-4
-/
def i2osp (n : Nat) (len : Nat) : ByteArray :=
  ⟨(Base.ByteOrder.toBE len n).toArray⟩

/-- `strxor(a, b)` of [RFC 9380 §4][utils]: the bitwise XOR of two byte strings.

The RFC defines it on two strings of one length.

On strings of two lengths, this function stops at the end of the shorter one.

The expansion calls it only on two 32-byte digests, `b_0` and `b_(i-1)`.

[utils]: https://www.rfc-editor.org/rfc/rfc9380#section-4
-/
def strxor (a b : ByteArray) : ByteArray :=
  -- XOR the bytes at each position.
  ⟨Array.zipWith (· ^^^ ·) a.data b.data⟩

/-- The block `b_i` of RFC 9380 §5.3.1, step 10, from `b_0`, `DST_prime` and `b_(i-1)`.

It is `b_i` for `2 <= i <= 255` when `prev` is `b_(i-1)`.

Step 8 computes `b_1` without the XOR, and the index is written in one byte. -/
def bI (b0 dstPrime prev : ByteArray) (i : Nat) : ByteArray :=
  -- Step 10: `b_i = H(strxor(b_0, b_(i - 1)) || I2OSP(i, 1) || DST_prime)`.
  Hash.Sha256.hash (strxor b0 prev ++ i2osp i 1 ++ dstPrime)

/-- The message expansion of [RFC 9380 §5.3.1][xmd], with SHA-256 as `H`.

It returns `len_in_bytes` uniform bytes, derived from the message under the tag.

Each step of the RFC is marked in the body by its number.

The RFC aborts on a tag longer than 255 bytes.

This function instead replaces such a tag by its hash, as [§5.3.3][long] specifies.

It rejects the two other cases of step 2 with a typed error.

[xmd]: https://www.rfc-editor.org/rfc/rfc9380#section-5.3.1
[long]: https://www.rfc-editor.org/rfc/rfc9380#section-5.3.3
-/
def expandMessageXmd
    (msg : ByteArray) (dst : ByteArray) (lenInBytes : Nat)
    : Except BlsError ByteArray := do
  -- Step 1: `ell = ceil(len_in_bytes / b_in_bytes)`, with `b_in_bytes = 32` for SHA-256.
  let ell := (lenInBytes + Hash.Sha256.DIGEST_SIZE_BYTES - 1) / Hash.Sha256.DIGEST_SIZE_BYTES
  -- Step 2: abort if `len_in_bytes > 65535`, since step 5 writes it in two bytes.
  if lenInBytes > 65535 then
    throw (.expandMessageOutputTooLong lenInBytes)
  -- Step 2: abort if `ell > 255`, since steps 8 and 10 write the index `i` in one byte.
  if ell > 255 then
    throw (.expandMessageTooManyBlocks ell)
  -- Step 2 aborts on a tag longer than 255 bytes, since step 3 writes its length in one byte.
  --
  -- §5.3.3 instead replaces the tag by `H("H2C-OVERSIZE-DST-" || DST)`, 32 bytes long.
  let dst :=
    if dst.size > 255 then
      Hash.Sha256.hash (oversizeDstPrefix ++ dst)
    else
      dst
  -- Step 3: `DST_prime = DST || I2OSP(len(DST), 1)`.
  let dstPrime := dst ++ i2osp dst.size 1
  -- Step 4: `Z_pad = I2OSP(0, s_in_bytes)`, with `s_in_bytes = 64` for SHA-256.
  let zPad := ByteArray.mk (Array.replicate Hash.Sha256.BLOCK_SIZE_BYTES 0)
  -- Step 5: `l_i_b_str = I2OSP(len_in_bytes, 2)`.
  let lIbStr := i2osp lenInBytes 2
  -- Step 6: `msg_prime = Z_pad || msg || l_i_b_str || I2OSP(0, 1) || DST_prime`.
  let msgPrime := zPad ++ msg ++ lIbStr ++ i2osp 0 1 ++ dstPrime
  -- Step 7: `b_0 = H(msg_prime)`.
  let b0 := Hash.Sha256.hash msgPrime
  -- Step 8: `b_1 = H(b_0 || I2OSP(1, 1) || DST_prime)`.
  let b1 := Hash.Sha256.hash (b0 ++ i2osp 1 1 ++ dstPrime)
  -- Step 11: `uniform_bytes = b_1 || ... || b_ell`, in a buffer sized for `ell` blocks.
  --
  -- It holds `b_1` alone when `ell <= 1`.
  let mut out := ByteArray.emptyWithCapacity (Hash.Sha256.DIGEST_SIZE_BYTES * ell) ++ b1
  -- The block `b_(i-1)` that the next step reads.
  let mut prev := b1
  -- Step 9: for `i` from 2 to `ell`.
  for i in [2:ell+1] do
    -- Step 10 computes `b_i` from `b_(i-1)`, and step 11 appends it.
    let bi := bI b0 dstPrime prev i
    out := out ++ bi
    prev := bi
  -- Step 12: the output is the first `len_in_bytes` bytes of `uniform_bytes`.
  return out.extract 0 lenInBytes

/-! ## Hash to the field `Fp2` (RFC 9380 §5.2)

The hash to the field of [RFC 9380 §5.2][h2f], for `F = GF(p^2)` with extension degree `m = 2`.

[h2f]: https://www.rfc-editor.org/rfc/rfc9380#section-5.2
-/

/-- `OS2IP(tv) mod p`, step 7 of [RFC 9380 §5.2][h2f].

OS2IP of [RFC 8017 §4.2][os2ip] reads the bytes as a big-endian integer.

[h2f]: https://www.rfc-editor.org/rfc/rfc9380#section-5.2
[os2ip]: https://www.rfc-editor.org/rfc/rfc8017#section-4.2
-/
def fpFromBytesL (b : ByteArray) : F :=
  -- The big-endian integer of the bytes, reduced mod `p` by the field.
  BaseField.ofNat (Base.ByteOrder.ofBE b.data.toList)

/-- The hash to the field of [RFC 9380 §5.2][h2f]: `count` elements of `Fp2` from the message.

The suite `BLS12381G2_XMD:SHA-256_SSWU_RO_` of [§8.8.2][suite] fixes the parameters:

- `m = 2`, since `Fp2` has degree 2 over `Fp`.
- `k = 128`, the target security level in bits.
- `L = ceil((ceil(log2(p)) + k) / 8) = ceil((381 + 128) / 8) = 64`.
- The message expansion is the one of §5.3.1, with SHA-256.

Each element reads `m * L = 128` bytes of the expansion.

Each step of the RFC is marked in the body by its number.

[h2f]: https://www.rfc-editor.org/rfc/rfc9380#section-5.2
[suite]: https://www.rfc-editor.org/rfc/rfc9380#section-8.8.2
-/
def hashToFieldFp2
    (msg : ByteArray) (dst : ByteArray) (count : Nat)
    : Except BlsError (Vector (Fp2 F) count) := do
  -- `L = 64` bytes per base-field element, from §8.8.2.
  let l := 64
  -- `m = 2` base-field elements per element of `Fp2`.
  let m := 2
  -- Step 1: `len_in_bytes = count * m * L`.
  let lenInBytes := count * m * l
  -- Step 2: `uniform_bytes` is the expansion of `msg` under `DST` to `len_in_bytes` bytes.
  let uniform ← expandMessageXmd msg dst lenInBytes
  -- Step 3: for `i` from 0 to `count - 1`.
  return Vector.ofFn fun i =>
    -- Steps 4 and 5: `elm_offset = L * (j + i * m)`, for `j = 0` and `j = 1`.
    let off0 := l * (i.val * m)
    let off1 := l * (i.val * m + 1)
    -- Steps 6 and 7: `e_j = OS2IP(substr(uniform_bytes, elm_offset, L)) mod p`.
    let c0 := fpFromBytesL (uniform.extract off0 (off0 + l))
    let c1 := fpFromBytesL (uniform.extract off1 (off1 + l))
    -- Step 8: `u_i = (e_0, e_1)`, the element `e_0 + e_1 * I`.
    -- Step 9 returns `(u_0, ..., u_(count - 1))`, the vector that this builds.
    ⟨c0, c1⟩

/-! ## SSWU map onto the 3-isogenous curve `E'` (RFC 9380 §6.6.3)

The twist `E : y^2 = x^3 + 4 * (1 + I)` has `A = 0`, so the simplified SWU map does not apply to it.

[RFC 9380 §6.6.3][ab0] maps to a curve `E'` with `A' B' ≠ 0`, then follows a 3-isogeny to `E`.

The constants are those of the suite `BLS12381G2_XMD:SHA-256_SSWU_RO_`, [§8.8.2][suite].

[ab0]: https://www.rfc-editor.org/rfc/rfc9380#section-6.6.3
[suite]: https://www.rfc-editor.org/rfc/rfc9380#section-8.8.2
-/

/-- `Z = -(2 + I)`, a non-square of `Fp2`, [RFC 9380 §8.8.2][suite].

[suite]: https://www.rfc-editor.org/rfc/rfc9380#section-8.8.2
-/
def Z : Fp2 F := ⟨-(BaseField.ofNat 2), -BaseField.one⟩

/-- `A' = 240 * I`, the coefficient of `x` in `E'`, [RFC 9380 §8.8.2][suite].

[suite]: https://www.rfc-editor.org/rfc/rfc9380#section-8.8.2
-/
def Aprime : Fp2 F := ⟨BaseField.zero, BaseField.ofNat 240⟩

/-- `B' = 1012 * (1 + I)`, the constant term of `E'`, [RFC 9380 §8.8.2][suite].

[suite]: https://www.rfc-editor.org/rfc/rfc9380#section-8.8.2
-/
def Bprime : Fp2 F := Fp2.ofNats 1012 1012

/-- The exponent `(p - 3) / 4`: one power by it gives a square root and an inverse.

For `a ≠ 0` and `r = a^((p - 3) / 4)`, `r a` squares to `a` or `-a`, and `r^2 a` is 1 or -1. -/
def rootExponent : Nat := (Fp.modulus - 3) / 4

/-- A square root of `-N(Z) = -5` in the base field, where `N(Z)` is the norm of `Z`. -/
def sqrtNegNormZ : F := BaseField.ofNat
  0x186417302d5a65347a88b0f999ab2b504614aa5e2eebdeb1a014c40bceb7d2306c12a6d436befcf94d39c9db7b263cd4

/-- `sqrt_ratio(u, v)` of [RFC 9380 Appendix F.2.1][ratio], for `v ≠ 0`, with no inversion of `v`.

- If `u / v` is a square, it returns `true` and a square root of `u / v`.
- Otherwise it returns `false` and a square root of `Z u / v`.

That is the output of Appendix F.2.1.1, and [§4][utils] fixes no root, since the map sets the sign.

It takes one power of the base field for the norms, then the root of the complex method.

[ratio]: https://www.rfc-editor.org/rfc/rfc9380#appendix-F.2.1
[utils]: https://www.rfc-editor.org/rfc/rfc9380#section-4
-/
def sqrtRatio (u v : Fp2 F) : Bool × Fp2 F :=
  -- The norms `N(u)` and `N(v)`, in the base field.
  let nu := u.c0 * u.c0 + u.c1 * u.c1
  let nv := v.c0 * v.c0 + v.c1 * v.c1
  -- `u / v = (u v) / v^2`, so `sqrt(u / v) = sqrt(u v) / v`, and `N(u v) = N(u) N(v)`.
  let alpha := nu * nv
  -- `u = 0`: the ratio is the square 0.
  if BaseField.isZero alpha then (true, Fp2.zero) else
    -- `r = alpha^((p - 3) / 4)`, and `e = r^2 alpha = alpha^((p - 1) / 2)` is 1 or -1.
    let r := BaseField.powNat alpha rootExponent
    let e := r * r * alpha
    -- `u v` is a square of `Fp2` exactly when its norm `alpha` is a square of the base field.
    let isQR := BaseField.beq e BaseField.one
    -- `s = r alpha` squares to `e alpha`: a root of `alpha`, or of `-alpha` when `isQR` fails.
    let s := r * alpha
    -- `1 / N(v) = N(u) / alpha`, and `1 / alpha = r^2 e`.
    let invNv := nu * (r * r) * e
    -- Otherwise the root is that of `Z u v`, whose norm `N(Z) alpha` has the root `sqrt(-N(Z)) s`.
    let w := if isQR then Fp2.sqrtOfNormRoot (u * v) s
      else Fp2.sqrtOfNormRoot (Z * (u * v)) (sqrtNegNormZ * s)
    -- `1 / v = conj(v) / N(v)`.
    (isQR, w * v.conjugate.mulFp invNv)

/-- The simplified SWU map of [RFC 9380 Appendix F.2][f2]: a point of `E'` for `u`.

The result `(xn, xd, y)` is the point `(xn / xd, y)`, with `xd ≠ 0`.

[f2]: https://www.rfc-editor.org/rfc/rfc9380#appendix-F.2
-/
def simpleSwu (u : Fp2 F) : Fp2 F × Fp2 F × Fp2 F :=
  -- Steps 1 and 2: `tv1 = Z * u^2`.
  let tv1 := Z * FieldOps.square u
  -- Steps 3 and 4: `tv2 = tv1^2 + tv1`.
  let tv2 := FieldOps.square tv1 + tv1
  -- Steps 5 and 6: `tv3 = B' * (tv2 + 1)`.
  let tv3 := Bprime * (tv2 + Fp2.one)
  -- Steps 7 and 8: `tv4 = A' * (tv2 ≠ 0 ? -tv2 : Z)`, so `x1 = tv3 / tv4`.
  let tv4 := Aprime * (if tv2.isZero then Z else -tv2)
  -- Step 10: `tv6 = tv4^2`.
  let tv6 := FieldOps.square tv4
  -- Steps 9, 11 to 13, 15 and 16: `gx1 = tv3^3 + A' tv3 tv4^2 + B' tv4^3 = g(x1) tv4^3`.
  --
  -- Here `g(x) = x^3 + A' * x + B'`, so `E' : y^2 = g(x)`.
  let gx1 := (FieldOps.square tv3 + Aprime * tv6) * tv3 + Bprime * (tv6 * tv4)
  -- Step 14: `tv6 = tv4^3`.
  let tv6 := tv6 * tv4
  -- Step 18: `y1 = sqrt(g(x1))`, or `sqrt(Z g(x1))` when `g(x1)` is not a square.
  let (isGx1Square, y1) := sqrtRatio gx1 tv6
  -- Steps 17 and 21: `x = x1 = tv3 / tv4`, or `x = x2 = tv1 tv3 / tv4`.
  let xn := if isGx1Square then tv3 else tv1 * tv3
  -- Steps 19, 20 and 22: `y = y1`, or `y = tv1 u y1`, a root of `g(x2) = tv1^3 g(x1)`.
  let y := if isGx1Square then y1 else tv1 * u * y1
  -- Steps 23 and 24: if `sgn0(u) ≠ sgn0(y)`, then `y = -y`.
  --
  -- Step 25, the division `x = xn / tv4`, is left to the isogeny, which needs none.
  (xn, tv4, if Fp2.sgn0 u = Fp2.sgn0 y then y else -y)

/-! ## 3-isogeny map `E' → E` (RFC 9380 Appendix E.3)

The rational map of [RFC 9380 Appendix E.3][iso], from `E'` to the twist `E`.

The constant `kIJ` is the coefficient `k_(I,J)` of the RFC, written as `c0 + c1 * I`.

- `k_(1,0)` to `k_(1,3)` are the coefficients of `x_num`.
- `k_(2,0)` and `k_(2,1)` are the coefficients of `x_den`.
- `k_(3,0)` to `k_(3,3)` are the coefficients of `y_num`.
- `k_(4,0)` to `k_(4,2)` are the coefficients of `y_den`.

[iso]: https://www.rfc-editor.org/rfc/rfc9380#appendix-E.3
-/

/-- `k_(1,0)`, the constant term of `x_num`. -/
def k10 : Fp2 F := Fp2.ofNats
  0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6
  0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6

/-- `k_(1,1)`, the coefficient of `x'` in `x_num`. -/
def k11 : Fp2 F := Fp2.ofNats
  0
  0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71a

/-- `k_(1,2)`, the coefficient of `x'^2` in `x_num`. -/
def k12 : Fp2 F := Fp2.ofNats
  0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71e
  0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38d

/-- `k_(1,3)`, the coefficient of `x'^3` in `x_num`. -/
def k13 : Fp2 F := Fp2.ofNats
  0x171d6541fa38ccfaed6dea691f5fb614cb14b4e7f4e810aa22d6108f142b85757098e38d0f671c7188e2aaaaaaaa5ed1
  0

/-- `k_(2,0)`, the constant term of `x_den`. -/
def k20 : Fp2 F := Fp2.ofNats
  0
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa63

/-- `k_(2,1)`, the coefficient of `x'` in `x_den`. -/
def k21 : Fp2 F := Fp2.ofNats
  0xc
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa9f

/-- `k_(3,0)`, the constant term of `y_num`. -/
def k30 : Fp2 F := Fp2.ofNats
  0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706
  0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706

/-- `k_(3,1)`, the coefficient of `x'` in `y_num`. -/
def k31 : Fp2 F := Fp2.ofNats
  0
  0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97be

/-- `k_(3,2)`, the coefficient of `x'^2` in `y_num`. -/
def k32 : Fp2 F := Fp2.ofNats
  0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71c
  0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38f

/-- `k_(3,3)`, the coefficient of `x'^3` in `y_num`. -/
def k33 : Fp2 F := Fp2.ofNats
  0x124c9ad43b6cf79bfbf7043de3811ad0761b0f37a1e26286b0e977c69aa274524e79097a56dc4bd9e1b371c71c718b10
  0

/-- `k_(4,0)`, the constant term of `y_den`. -/
def k40 : Fp2 F := Fp2.ofNats
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb

/-- `k_(4,1)`, the coefficient of `x'` in `y_den`. -/
def k41 : Fp2 F := Fp2.ofNats
  0
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa9d3

/-- `k_(4,2)`, the coefficient of `x'^2` in `y_den`. -/
def k42 : Fp2 F := Fp2.ofNats
  0x12
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa99

/-- The 3-isogeny of [RFC 9380 Appendix E.3][iso], from the point `(xn / xd, y')` of `E'` to `E`.

The result is in Jacobian coordinates, by [Appendix G.1][g1], so it needs no inversion.

A zero denominator gives the identity point, as [§6.6.3][ab0] requires, and so does `xd = 0`.

[iso]: https://www.rfc-editor.org/rfc/rfc9380#appendix-E.3
[g1]: https://www.rfc-editor.org/rfc/rfc9380#appendix-G.1
[ab0]: https://www.rfc-editor.org/rfc/rfc9380#section-6.6.3
-/
def isoMapG2 (p : Fp2 F × Fp2 F × Fp2 F) : G2 F :=
  let xn := p.1
  let xd := p.2.1
  -- The monomials of degree 2 and 3 in `xn` and `xd`, shared by the four polynomials.
  let xn2 := FieldOps.square xn
  let xd2 := FieldOps.square xd
  let xn3 := xn2 * xn
  let xn2xd := xn2 * xd
  let xnxd2 := xn * xd2
  let xd3 := xd2 * xd
  -- Each polynomial at `x' = xn / xd`, times `xd^3`.
  --
  -- `x_num = k_(1,3) * x'^3 + k_(1,2) * x'^2 + k_(1,1) * x' + k_(1,0)`.
  let xNum := k13 * xn3 + k12 * xn2xd + k11 * xnxd2 + k10 * xd3
  -- `x_den = x'^2 + k_(2,1) * x' + k_(2,0)`, of degree 2, so times `xd^2`, then times `xd`.
  let xDen := (xn2 + k21 * (xn * xd) + k20 * xd2) * xd
  -- `y_num = k_(3,3) * x'^3 + k_(3,2) * x'^2 + k_(3,1) * x' + k_(3,0)`, times `y'`.
  let yNum := p.2.2 * (k33 * xn3 + k32 * xn2xd + k31 * xnxd2 + k30 * xd3)
  -- `y_den = x'^3 + k_(4,2) * x'^2 + k_(4,1) * x' + k_(4,0)`.
  let yDen := xn3 + k42 * xn2xd + k41 * xnxd2 + k40 * xd3
  -- So `x = xNum / xDen` and `y = yNum / yDen`.
  --
  -- `x_den` is monic of degree 2, and `y_den` is monic of degree 3.
  if xDen.isZero || yDen.isZero then G2.zero else
    -- Appendix G.1: `(X, Y, Z) = (xn * xd * yd^2, yn * yd^2 * xd^3, xd * yd)`.
    let yDen2 := FieldOps.square yDen
    let z := xDen * yDen
    ⟨xNum * xDen * yDen2, yNum * yDen2 * (FieldOps.square xDen * xDen), z⟩

/-! ## Cofactor clearing (RFC 9380 Appendix G.3)

The cofactor clearing sends a point of the twist to the subgroup `G2` of order `r`.

[RFC 9380 Appendix G.3][g3] computes it with the endomorphism `psi`.

That is the method of Budroni and Pintore.

It gives the same result as the multiplication by `h_eff` of [§7][clear].

[g3]: https://www.rfc-editor.org/rfc/rfc9380#appendix-G.3
[clear]: https://www.rfc-editor.org/rfc/rfc9380#section-7
-/

-- The endomorphism `psi` is a map of the twist, so it is defined with the curve.
export EthLib.Cryptography.Bls.G2 (c1Psi c2Psi psi)

/-- The constant `c1 = 1 / 2^((p - 1) / 3)` of `psi2`, [RFC 9380 Appendix G.3][g3].

It lies in `Fp`, and the map multiplies `x` by it as an element of `Fp2`.

[g3]: https://www.rfc-editor.org/rfc/rfc9380#appendix-G.3
-/
def c1Psi2 : Fp2 F :=
  let two : F := BaseField.ofNat 2
  let v : F := BaseField.inverse (BaseField.powNat two ((Fp.modulus - 1) / 3))
  ⟨v, BaseField.zero⟩

/-- `psi2(P) = (c1 * x, -y)`, the map `psi` applied twice, [RFC 9380 Appendix G.3][g3].

The RFC writes it on fractions `(xn / xd, yn / yd)`.

This is its affine form, with the denominators equal to 1.

[g3]: https://www.rfc-editor.org/rfc/rfc9380#appendix-G.3
-/
def psi2 (P : G2 F) : G2 F :=
  -- The point at infinity maps to itself.
  if P.z.isZero then P else
    -- Normalise to affine form, then map the coordinates, with `Z = 1`.
    let (x, y) := P.toAffine
    ⟨c1Psi2 * x, -y, Fp2.one⟩

/-- `[c1] P`, with `c1 = -0xd201000000010000` the BLS parameter, [RFC 9380 Appendix G.3][g3].

The parameter is negative, so this is `-[|c1|] P`.

[g3]: https://www.rfc-editor.org/rfc/rfc9380#appendix-G.3
-/
def mulNegX (P : G2 F) : G2 F := G2.neg (P.mulNat blsX)

/-- The cofactor clearing of `P` for `G2` of BLS12-381, by [RFC 9380 Appendix G.3][g3].

Each step of the RFC is marked in the body by its number.

[g3]: https://www.rfc-editor.org/rfc/rfc9380#appendix-G.3
-/
def clearCofactor (P : G2 F) : G2 F :=
  -- Step 1: `t1 = c1 * P`.
  let t1 := mulNegX P
  -- Step 2: `t2 = psi(P)`.
  let t2 := psi P
  -- Steps 3 and 4: `t3 = 2 * P`, then `t3 = psi2(t3)`.
  let t3 := psi2 P.double
  -- Step 5: `t3 = t3 - t2`.
  let t3 := G2.add t3 (G2.neg t2)
  -- Step 6: `t2 = t1 + t2`.
  let t2 := G2.add t1 t2
  -- Step 7: `t2 = c1 * t2`.
  let t2 := mulNegX t2
  -- Step 8: `t3 = t3 + t2`.
  let t3 := G2.add t3 t2
  -- Step 9: `t3 = t3 - t1`.
  let t3 := G2.add t3 (G2.neg t1)
  -- Steps 10 and 11: the output is `Q = t3 - P`.
  G2.add t3 (G2.neg P)

/-- The scalar `h_eff` of the suites for `G2` of BLS12-381, RFC 9380 §8.8.2.

RFC 9380 §7 defines the cofactor clearing as the multiplication by `h_eff`.

The cofactor clearing above uses the faster method of Appendix G.3 instead.

The three hexadecimal parts are the three lines of the value in the RFC. -/
def H_EFF_G2 : Nat :=
  0xbc69f08f2ee75b3584c6a0ea91b352888e2a8e9145ad7689986ff0315 * 16 ^ 102 +
    0x08ffe1329c2f178731db956d82bf015d1212b02ec0ec69d7477c1ae954cbc06689 * 16 ^ 36 +
    0xf6a359894c0adebbf6b4e8020005aaa95551

/-! ## Top-level pipeline -/

/-- The hash to curve of [RFC 9380 §3][h2c], for the suite `BLS12381G2_XMD:SHA-256_SSWU_RO_`.

The result is a point of the subgroup `G2`, derived from the message under the tag.

The map to the curve is the simplified SWU map to `E'`, then the 3-isogeny to `E`, by [§6.6.3][ab0].

Each step of the RFC is marked in the body by its number.

[h2c]: https://www.rfc-editor.org/rfc/rfc9380#section-3
[ab0]: https://www.rfc-editor.org/rfc/rfc9380#section-6.6.3
-/
def hashToG2 (msg : ByteArray) (dst : ByteArray) : Except BlsError (G2 F) := do
  -- Step 1: `u` is the pair of elements of `Fp2` that the hash to the field gives for `msg`.
  let us ← hashToFieldFp2 msg dst 2
  -- Steps 2 and 3: `Q0` and `Q1` are the images of `u[0]` and `u[1]` on `E`.
  --
  -- Each is the image by the SSWU map to `E'`, then by the 3-isogeny to `E`.
  --
  -- Step 4: `R = Q0 + Q1`.
  --
  -- Steps 5 and 6: the output `P` is `R` with its cofactor cleared.
  return clearCofactor (G2.add (isoMapG2 (simpleSwu us[0])) (isoMapG2 (simpleSwu us[1])))

end EthLib.Cryptography.Bls.HashToCurve
