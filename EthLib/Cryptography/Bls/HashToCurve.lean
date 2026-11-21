module

public import EthLib.Cryptography.Bls.G2
public import EthLib.Cryptography.Bls.Errors
public import EthLib.Cryptography.Hash.Sha256
public import EthLib.Base.BigEndian

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

/-! ## `expand_message_xmd` (RFC 9380 §5.3.1)

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
  ByteArray.mk <| Array.ofFn (n := len) fun i =>
    -- Byte `i` holds bits `8 (len - 1 - i)` to `8 (len - 1 - i) + 7` of `n`.
    -- So byte 0 holds the most significant byte, as big-endian order requires.
    UInt8.ofNat ((n >>> ((len - 1 - i.val) * 8)) &&& 0xff)

/-- `strxor(a, b)` of [RFC 9380 §4][utils]: the bitwise XOR of two byte strings.

The RFC defines it on two strings of one length.

On strings of two lengths, this function stops at the end of the shorter one.

The expansion calls it only on two 32-byte digests, `b_0` and `b_(i-1)`.

[utils]: https://www.rfc-editor.org/rfc/rfc9380#section-4
-/
def strxor (a b : ByteArray) : ByteArray :=
  -- XOR the bytes at each position.
  ⟨Array.zipWith (· ^^^ ·) a.data b.data⟩

/-- `expand_message_xmd(msg, DST, len_in_bytes)` of [RFC 9380 §5.3.1][xmd], with SHA-256 as `H`.

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
  -- Step 2 aborts if `len(DST) > 255`, since step 3 writes the length in one byte.
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
  -- The blocks `b_1` to `b_ell`, in order.
  let mut bs : Array ByteArray := Array.mkEmpty ell
  -- Step 8: `b_1 = H(b_0 || I2OSP(1, 1) || DST_prime)`.
  let b1 := Hash.Sha256.hash (b0 ++ i2osp 1 1 ++ dstPrime)
  bs := bs.push b1
  -- The block `b_(i-1)` that the next step reads.
  let mut prev := b1
  -- Step 9: for `i` from 2 to `ell`.
  for i in [2:ell+1] do
    -- Step 10: `b_i = H(strxor(b_0, b_(i-1)) || I2OSP(i, 1) || DST_prime)`.
    let bi := Hash.Sha256.hash (strxor b0 prev ++ i2osp i 1 ++ dstPrime)
    bs := bs.push bi
    prev := bi
  -- Step 11: `uniform_bytes = b_1 || ... || b_ell`.
  let mut out := bs.foldl (· ++ ·) ByteArray.empty
  -- Step 12: `return substr(uniform_bytes, 0, len_in_bytes)`.
  return out.extract 0 lenInBytes

/-! ## `hash_to_field` for Fp2 (RFC 9380 §5.2)

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
  BaseField.ofNat (Base.bytesToNat b.data.toList)

/-- `hash_to_field(msg, count)` of [RFC 9380 §5.2][h2f]: `count` elements of `Fp2`.

The suite `BLS12381G2_XMD:SHA-256_SSWU_RO_` of [§8.8.2][suite] fixes the parameters:

- `m = 2`, since `Fp2` has degree 2 over `Fp`.
- `k = 128`, the target security level in bits.
- `L = ceil((ceil(log2(p)) + k) / 8) = ceil((381 + 128) / 8) = 64`.
- The message expansion is `expand_message_xmd` with SHA-256.

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
  -- Step 2: `uniform_bytes = expand_message(msg, DST, len_in_bytes)`.
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

[RFC 9380 §6.6.3][ab0] maps to a curve `E'` with `A' B' != 0`, then follows a 3-isogeny to `E`.

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

/-- `map_to_curve_simple_swu(u)` of [RFC 9380 §6.6.2][sswu]: a point of `E' : y^2 = g(x)`.

Here `g(x) = x^3 + A' * x + B'`.

Each step of the RFC is marked in the body by its number.

`Z` is not a square in `Fp2`, so `g(x1)` or `g(x2)` is a square.

The error is the case where neither is, which that choice of `Z` excludes.

[sswu]: https://www.rfc-editor.org/rfc/rfc9380#section-6.6.2
-/
def simpleSwu (u : Fp2 F) : Except BlsError (Fp2 F × Fp2 F) := do
  let u2 := u * u
  let zu2 := Z * u2
  -- The denominator `Z^2 * u^4 + Z * u^2` of step 1.
  let denom := zu2 * zu2 + zu2
  let x1 :=
    -- Step 1: `tv1 = inv0(Z^2 * u^4 + Z * u^2)`, which is 0 exactly when the denominator is.
    if denom.isZero then
      -- Step 3: if `tv1 == 0`, set `x1 = B' / (Z * A')`.
      -- The denominator is 0 when `Z * u^2` is 0 or -1.
      Bprime / (Z * Aprime)
    else
      -- Step 2: `x1 = (-B' / A') * (1 + tv1)`.
      (-Bprime / Aprime) * (Fp2.one + denom.inverse)
  -- Step 4: `gx1 = x1^3 + A' * x1 + B'`.
  let gx1 : Fp2 F := x1 * x1 * x1 + Aprime * x1 + Bprime
  match Fp2.sqrt gx1 with
  | some y =>
    -- Step 7: `gx1` is a square, so `x = x1` and `y = sqrt(gx1)`.
    -- Step 9: if `sgn0(u) != sgn0(y)`, set `y = -y`.
    return (x1, if Fp2.sgn0 u = Fp2.sgn0 y then y else -y)
  | none =>
    -- Step 5: `x2 = Z * u^2 * x1`, needed only when `gx1` is not a square.
    let x2 := zu2 * x1
    -- Steps 6 and 8: `x = x2` and `y = sqrt(gx2)`, with `gx2 = x2^3 + A' * x2 + B'`.
    match Fp2.sqrt (x2 * x2 * x2 + Aprime * x2 + Bprime : Fp2 F) with
    | none => .error .notASquare
    | some y =>
      -- Step 9: if `sgn0(u) != sgn0(y)`, set `y = -y`.
      return (x2, if Fp2.sgn0 u = Fp2.sgn0 y then y else -y)

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

/-- The 3-isogeny `iso_map` of [RFC 9380 Appendix E.3][iso], from `(x', y')` on `E'` to `E`.

- `x = x_num / x_den`, where `x_den` is monic of degree 2.
- `y = y' * y_num / y_den`, where `y_den` is monic of degree 3.

A zero denominator gives the identity point, as [§6.6.3][ab0] requires.

[iso]: https://www.rfc-editor.org/rfc/rfc9380#appendix-E.3
[ab0]: https://www.rfc-editor.org/rfc/rfc9380#section-6.6.3
-/
def isoMapG2 (xp yp : Fp2 F) : G2 F :=
  -- The powers `x'^2` and `x'^3`, shared by the four polynomials.
  let xp2 := xp * xp
  let xp3 := xp2 * xp
  -- `x_num = k_(1,3) * x'^3 + k_(1,2) * x'^2 + k_(1,1) * x' + k_(1,0)`.
  let xNum := k13 * xp3 + k12 * xp2 + k11 * xp + k10
  -- `x_den = x'^2 + k_(2,1) * x' + k_(2,0)`.
  let xDen := xp2 + k21 * xp + k20
  -- `y_num = k_(3,3) * x'^3 + k_(3,2) * x'^2 + k_(3,1) * x' + k_(3,0)`.
  let yNum := k33 * xp3 + k32 * xp2 + k31 * xp + k30
  -- `y_den = x'^3 + k_(4,2) * x'^2 + k_(4,1) * x' + k_(4,0)`.
  let yDen := xp3 + k42 * xp2 + k41 * xp + k40
  -- `x = x_num / x_den` and `y = y' * y_num / y_den`, as the affine point with `Z = 1`.
  if xDen.isZero || yDen.isZero then G2.zero else ⟨xNum / xDen, yp * yNum / yDen, Fp2.one⟩

/-! ## Cofactor clearing (RFC 9380 Appendix G.3)

`clear_cofactor` sends a point of the twist to the subgroup `G2` of order `r`.

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
def mulNegX (P : G2 F) : G2 F := G2.neg (G2.mulNat P blsX)

/-- `clear_cofactor_bls12381_g2(P)` of [RFC 9380 Appendix G.3][g3].

Each step of the RFC is marked in the body by its number.

[g3]: https://www.rfc-editor.org/rfc/rfc9380#appendix-G.3
-/
def clearCofactor (P : G2 F) : G2 F :=
  -- Step 1: `t1 = c1 * P`.
  let t1 := mulNegX P
  -- Step 2: `t2 = psi(P)`.
  let t2 := psi P
  -- Steps 3 and 4: `t3 = 2 * P`, then `t3 = psi2(t3)`.
  let t3 := psi2 (G2.double P)
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
  -- Steps 10 and 11: `Q = t3 - P`, then `return Q`.
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

/-- `hash_to_curve(msg)` of [RFC 9380 §3][h2c], for the suite `BLS12381G2_XMD:SHA-256_SSWU_RO_`.

The result is a point of the subgroup `G2`, derived from the message under the tag.

`map_to_curve` is the simplified SWU map to `E'`, then the 3-isogeny to `E`, by [§6.6.3][ab0].

Each step of the RFC is marked in the body by its number.

[h2c]: https://www.rfc-editor.org/rfc/rfc9380#section-3
[ab0]: https://www.rfc-editor.org/rfc/rfc9380#section-6.6.3
-/
def hashToG2 (msg : ByteArray) (dst : ByteArray) : Except BlsError (G2 F) := do
  -- Step 1: `u = hash_to_field(msg, 2)`.
  let us ← hashToFieldFp2 msg dst 2
  -- Steps 2 and 3, first half: the simplified SWU map of `u[0]` and `u[1]` to `E'`.
  let (x0, y0) ← simpleSwu us[0]
  let (x1, y1) ← simpleSwu us[1]
  -- Steps 2 and 3, second half: `Q0` and `Q1` are the images on `E` by the 3-isogeny.
  -- Step 4: `R = Q0 + Q1`.
  -- Steps 5 and 6: `P = clear_cofactor(R)`, then `return P`.
  return clearCofactor (G2.add (isoMapG2 x0 y0) (isoMapG2 x1 y1))

end EthLib.Cryptography.Bls.HashToCurve
