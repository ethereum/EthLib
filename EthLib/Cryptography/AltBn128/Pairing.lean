module

public import EthLib.Cryptography.AltBn128.Curve
public import EthLib.Cryptography.Fp2

/-!
# `AltBn128.Pairing`

The optimal ate pairing of alt_bn128, which EIP-197 checks products of.

The pairing maps a point of `G_1` and a point of `G_2` to `Fp12`.

It is bilinear: `e(a P, b Q) = e(P, Q)^(a b)`.

It uses two extension fields of `Fp`:

- `Fp2 = Fp[i] / (i^2 + 1)`, where the points of `G_2` live.
- `Fp12 = Fp[w] / (w^12 - 18 w^6 + 82)`, where the pairing lands.
- `Fp2` sits inside `Fp12` by `a + b i -> (a - 9 b) + b w^6`, since `(w^6 - 9)^2 = -1` there.
-/

@[expose] public section

namespace EthLib.Cryptography.AltBn128

/-! ## `Fp2` -/

/-- The quadratic extension `Fp2 = Fp[i] / (i^2 + 1)`, with elements `c0 + c1 i`.

[EIP-197](https://eips.ethereum.org/EIPS/eip-197), §"Definition of the groups", defines this field.

It is the generic quadratic extension, at the base field `Fp`. -/
abbrev Fp2 : Type := Cryptography.Fp2 Fp

namespace Fp2

-- The operations of the generic extension keep their names here.
export Cryptography.Fp2 (mk add sub mul neg)

/-- The element of `Fp`. -/
abbrev ofFp (a : Fp) : Fp2 := Cryptography.Fp2.ofFp a

/-- The element `i`. -/
abbrev i : Fp2 := Cryptography.Fp2.i

/-- The conjugate `c0 - c1 i`, which is also `a^p`. -/
abbrev conj (a : Fp2) : Fp2 := a.conjugate

/-- The inverse: `(c0 - c1 i) / (c0^2 + c1^2)`, and 0 for 0. -/
abbrev inv (a : Fp2) : Fp2 := a.inverse

end Fp2

/-! ## The twist and `G_2` -/

-- `G_2` lies on the twist `y^2 = x^3 + 3 / (9 + i)` over `Fp2`.
--
-- The twist sends `(x, y)` to `(x w^2, y w^3)` on `y^2 = x^3 + 3` over `Fp12`.
/-- `b2 = 3 / (9 + i)`, the constant of the twist, from EIP-197. -/
def b2 : Fp2 := Fp2.mul (Fp2.ofFp 3) (Fp2.inv ⟨9, 1⟩)

/-- The numeral `2` of `Fp2`, the element `2` of `Fp`. -/
instance instOfNatTwo : OfNat Fp2 2 := ⟨Fp2.ofFp 2⟩

/-- The numeral `3` of `Fp2`, the element `3` of `Fp`. -/
instance instOfNatThree : OfNat Fp2 3 := ⟨Fp2.ofFp 3⟩

/-- The twist as a short Weierstrass curve, with `a = 0`, `b2`, and the inverse of `Fp2`.

Its points then add by the rule of SEC 1 v2 §2.2.1, which `G_1` uses over `Fp`. -/
instance instTwistParams : ShortWeierstrass.Params Fp2 := ⟨0, b2, Fp2.inv⟩

/-- A point of the twist over `Fp2`, or the point at infinity. -/
abbrev Point2 := ShortWeierstrass.Point Fp2

namespace Point2

-- The constructors are restated at the twist's point type, under the names of the twist.

/-- The point at infinity, the zero of the group. -/
@[match_pattern] abbrev infinity : Point2 := ShortWeierstrass.Point.infinity

/-- The point `(x, y)`. -/
@[match_pattern] abbrev affine (x y : Fp2) : Point2 := ShortWeierstrass.Point.affine x y

/-- The generator `P2` of `G_2`, from EIP-197 §"Definition of the groups".

EIP-197 writes each coordinate as `c1 i + c0`. -/
def generator : Point2 :=
  affine
    ⟨10857046999023057135944570762232829481370756359578518086990519993285655852781,
      11559732032986387107991004021392285783925812861821192530917403151452391805634⟩
    ⟨8495653923123431417604973247489272438418190587263600148770280649306958101930,
      4082367875863433681332203403145435568316851327593401208105741076214120093531⟩

/-- `k P`, for `k < 2^fuel`, by double and add on the bits of `k`, low bit first.

The steps run in Jacobian coordinates over `Fp2`, with the twist's `a = 0`.

Only the conversion back takes an inverse. -/
def mulBits (fuel k : Nat) (p : Point2) : Point2 :=
  ShortWeierstrass.Point.mulBits id Fp2.inv id 0 fuel k p

end Point2

/-! ## `Fp12` -/

/-- An element of `Fp12`: the coefficients of `1, w, ..., w^11`. -/
abbrev Fp12 := Vector Fp 12

namespace Fp12

/-- The element 1. -/
def one : Fp12 := Vector.ofFn fun k => if k.val = 0 then 1 else 0

/-- The element of `Fp`. -/
def ofFp (a : Fp) : Fp12 := Vector.ofFn fun k => if k.val = 0 then a else 0

/-- The element `a + b i` of `Fp2`, as `(a - 9 b) + b w^6`. -/
def ofFp2 (a : Fp2) : Fp12 :=
  Vector.ofFn fun k => if k.val = 0 then a.c0 - 9 * a.c1 else if k.val = 6 then a.c1 else 0

/-- `w^k`. -/
def wPow (k : Fin 12) : Fp12 := Vector.ofFn fun j => if j = k then 1 else 0

/-- The sum, coefficient by coefficient. -/
def add (a b : Fp12) : Fp12 := Vector.ofFn fun k => a[k] + b[k]

/-- The difference, coefficient by coefficient. -/
def sub (a b : Fp12) : Fp12 := Vector.ofFn fun k => a[k] - b[k]

/-- The product: the product of the polynomials, reduced with `w^12 = 18 w^6 - 82`.

The sums are taken on the values in `Nat`, and each coefficient is reduced modulo `p` once. -/
def mul (a b : Fp12) : Fp12 :=
  let x0 := a[0].val; let x1 := a[1].val; let x2 := a[2].val; let x3 := a[3].val
  let x4 := a[4].val; let x5 := a[5].val; let x6 := a[6].val; let x7 := a[7].val
  let x8 := a[8].val; let x9 := a[9].val; let x10 := a[10].val; let x11 := a[11].val
  let y0 := b[0].val; let y1 := b[1].val; let y2 := b[2].val; let y3 := b[3].val
  let y4 := b[4].val; let y5 := b[5].val; let y6 := b[6].val; let y7 := b[7].val
  let y8 := b[8].val; let y9 := b[9].val; let y10 := b[10].val; let y11 := b[11].val
  -- The coefficient of `w^m` in the product of the polynomials is `c_m`, for `m ≤ 22`.
  let c0 := x0 * y0
  let c1 := x0 * y1 + x1 * y0
  let c2 := x0 * y2 + x1 * y1 + x2 * y0
  let c3 := x0 * y3 + x1 * y2 + x2 * y1 + x3 * y0
  let c4 := x0 * y4 + x1 * y3 + x2 * y2 + x3 * y1 + x4 * y0
  let c5 := x0 * y5 + x1 * y4 + x2 * y3 + x3 * y2 + x4 * y1 + x5 * y0
  let c6 := x0 * y6 + x1 * y5 + x2 * y4 + x3 * y3 + x4 * y2 + x5 * y1 + x6 * y0
  let c7 := x0 * y7 + x1 * y6 + x2 * y5 + x3 * y4 + x4 * y3 + x5 * y2 + x6 * y1 + x7 * y0
  let c8 := x0 * y8 + x1 * y7 + x2 * y6 + x3 * y5 + x4 * y4 + x5 * y3 + x6 * y2 + x7 * y1 + x8 * y0
  let c9 := x0 * y9 + x1 * y8 + x2 * y7 + x3 * y6 + x4 * y5 + x5 * y4 + x6 * y3 + x7 * y2 +
    x8 * y1 + x9 * y0
  let c10 := x0 * y10 + x1 * y9 + x2 * y8 + x3 * y7 + x4 * y6 + x5 * y5 + x6 * y4 + x7 * y3 +
    x8 * y2 + x9 * y1 + x10 * y0
  let c11 := x0 * y11 + x1 * y10 + x2 * y9 + x3 * y8 + x4 * y7 + x5 * y6 + x6 * y5 + x7 * y4 +
    x8 * y3 + x9 * y2 + x10 * y1 + x11 * y0
  let c12 := x1 * y11 + x2 * y10 + x3 * y9 + x4 * y8 + x5 * y7 + x6 * y6 + x7 * y5 + x8 * y4 +
    x9 * y3 + x10 * y2 + x11 * y1
  let c13 := x2 * y11 + x3 * y10 + x4 * y9 + x5 * y8 + x6 * y7 + x7 * y6 + x8 * y5 + x9 * y4 +
    x10 * y3 + x11 * y2
  let c14 := x3 * y11 + x4 * y10 + x5 * y9 + x6 * y8 + x7 * y7 + x8 * y6 + x9 * y5 + x10 * y4 +
    x11 * y3
  let c15 := x4 * y11 + x5 * y10 + x6 * y9 + x7 * y8 + x8 * y7 + x9 * y6 + x10 * y5 + x11 * y4
  let c16 := x5 * y11 + x6 * y10 + x7 * y9 + x8 * y8 + x9 * y7 + x10 * y6 + x11 * y5
  let c17 := x6 * y11 + x7 * y10 + x8 * y9 + x9 * y8 + x10 * y7 + x11 * y6
  let c18 := x7 * y11 + x8 * y10 + x9 * y9 + x10 * y8 + x11 * y7
  let c19 := x8 * y11 + x9 * y10 + x10 * y9 + x11 * y8
  let c20 := x9 * y11 + x10 * y10 + x11 * y9
  let c21 := x10 * y11 + x11 * y10
  let c22 := x11 * y11
  -- Each `w^m` with `m ≥ 12` is `18 w^(m - 6) - 82 w^(m - 12)`.
  --
  -- So the terms of `w^18` to `w^22` first fold into those of `w^12` to `w^16`.
  --
  -- The terms of `w^12` to `w^16`, once those of `w^18` to `w^22` folded into them.
  let d12 := c12 + 18 * c18
  let d13 := c13 + 18 * c19
  let d14 := c14 + 18 * c20
  let d15 := c15 + 18 * c21
  let d16 := c16 + 18 * c22
  let f (n : Nat) : Fp := Fin.ofNat Fp.modulus n
  #v[f c0 - f (82 * d12), f c1 - f (82 * d13), f c2 - f (82 * d14), f c3 - f (82 * d15),
    f c4 - f (82 * d16), f c5 - f (82 * c17), f (c6 + 18 * d12) - f (82 * c18),
    f (c7 + 18 * d13) - f (82 * c19), f (c8 + 18 * d14) - f (82 * c20),
    f (c9 + 18 * d15) - f (82 * c21), f (c10 + 18 * d16) - f (82 * c22), f (c11 + 18 * c17)]

instance : Add Fp12 := ⟨add⟩
instance : Sub Fp12 := ⟨sub⟩
instance : Mul Fp12 := ⟨mul⟩

/-- `a^e`, for `e < 2^fuel`, by square and multiply on the bits of `e`. -/
def powBits : Nat → Fp12 → Nat → Fp12
  | 0, _, _ => one
  | fuel + 1, a, e =>
    let half := powBits fuel (a * a) (e / 2)
    if e % 2 = 1 then a * half else half

/-- `c a`, coefficient by coefficient. -/
def scale (c : Fp) (a : Fp12) : Fp12 := Vector.ofFn fun k => c * a[k]

/-- `w^(p - 1)` as an element of `Fp2`: `(9 + i)^((p - 1) / 6)`, since `w^6 = 9 + i`. -/
def frobeniusGamma : Fp2 := Fp2.powNat ⟨9, 1⟩ ((Fp.modulus - 1) / 6)

/-- The powers `(w^p)^k` for `k < 12`, which are also `(w^k)^p`.

`6` divides `p - 1`, so `w^p = w (w^6)^((p - 1) / 6)` is `w` times an element of `Fp2`.

Each exponent `k` is below `2^4`, so four bits of square and multiply reach it. -/
def frobeniusCoefficients : Vector Fp12 12 :=
  let wp := wPow 1 * ofFp2 frobeniusGamma
  Vector.ofFn fun k => powBits 4 wp k.val

/-- The `p`-th power.

Each coefficient `a_k` lies in `Fp`, so `a_k^p = a_k`.

So `(sum_k a_k w^k)^p = sum_k a_k (w^p)^k`. -/
def frobenius (a : Fp12) : Fp12 :=
  Fin.foldl 12 (fun acc k => acc + scale a[k] frobeniusCoefficients[k]) (ofFp 0)

/-- The `p^n`-th power, by `n` applications of the `p`-th power. -/
def frobeniusPow : Nat → Fp12 → Fp12
  | 0, a => a
  | n + 1, a => frobeniusPow n (frobenius a)

/-- The inverse, and 0 for 0.

The product `g` of the conjugates `a^p, ..., a^(p^11)` makes `a g` the norm of `a`, in `Fp`.

So `a^(-1) = g / (a g)`, with one inverse in `Fp`. -/
def inverse (a : Fp12) : Fp12 :=
  let (g, _) := (List.range 11).foldl (fun (g, c) _ =>
    let c := frobenius c
    (g * c, c)) (one, a)
  scale (a * g)[0].inv g

end Fp12

/-! ## The pairing -/

/-- The count `6 u + 2` of the Miller loop, for the BN parameter `u = 4965661367192848881`. -/
def ATE_LOOP_COUNT : Nat := 29793968203157093288

/-- The bit that the loop starts from.

The count has 65 bits, and its top bit 64 is the starting point `q`. -/
def LOG_ATE_LOOP_COUNT : Nat := 63

/-- The line of slope `l w` through the twisted point `(x1 w^2, y1 w^3)`, at `(xt, yt)`.

It is `l w (xt - x1 w^2) - (yt - y1 w^3)`. -/
def slopeLine (l x1 y1 : Fp2) (xt yt : Fp) : Fp12 :=
  -- An element `a + b i` of `Fp2` is `(a - 9 b) + b w^6` in `Fp12`, so the line has a closed form.
  --
  -- Write `l = l0 + l1 i` and `y1 - l x1 = d0 + d1 i`.
  let d := y1 - l * x1
  -- Then the line is `-yt + xt (l0 - 9 l1) w + (d0 - 9 d1) w^3 + xt l1 w^7 + d1 w^9`.
  #v[-yt, xt * (l.c0 - 9 * l.c1), 0, d.c0 - 9 * d.c1, 0, 0, 0, xt * l.c1, 0, d.c1, 0, 0]

/-- The vertical line `xt - x1 w^2` through the twisted point with `x` coordinate `x1 w^2`.

With `x1 = a + b i`, it is `xt - (a - 9 b) w^2 - b w^8`. -/
def verticalLine (x1 : Fp2) (xt : Fp) : Fp12 :=
  #v[xt, 0, -(x1.c0 - 9 * x1.c1), 0, 0, 0, 0, 0, -x1.c1, 0, 0, 0]

/-- The line through the twisted points `r` and `q`, at the point `(xt, yt)` of `G_1`.

It follows the line function of [the pairing-friendly curves draft][pfc], Appendix A.

The draft writes it on `E`, and here it runs on the twisted points.

[pfc]: https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-pairing-friendly-curves-11#appendix-A
-/
def linefunc (r q : Point2) (xt yt : Fp) : Fp12 :=
  -- Each line of the loop is evaluated in `Fp12`, at the twisted points.
  --
  -- A twisted point has `x` times `w^2` and `y` times `w^3`.
  --
  -- So a slope `l` of the twist is the slope `l w` of the twisted points.
  match r, q with
  | .affine x1 y1, .affine x2 y2 =>
    -- The draft tests `Q_1 = Q_2`, then `Q_1 = -Q_2`; on the curve, both have `x_1 = x_2`.
    if x1 ≠ x2 then
      -- Distinct `x`: the slope is `l = (y_2 - y_1) / (x_2 - x_1)`.
      --
      -- The line is then `l (x - x_1) + y_1 - y`.
      slopeLine ((y2 - y1) * (x2 - x1).inv) x1 y1 xt yt
    else if y1 = y2 then
      -- `Q_1 = Q_2`: the slope is `l = 3 x_1^2 / (2 y_1)`, and the line is the same.
      slopeLine (3 * x1 * x1 * Fp2.inv (2 * y1)) x1 y1 xt yt
    else
      -- `Q_1 = -Q_2`: the line is the vertical `x - x_1`.
      verticalLine x1 xt
  -- The loop never meets the point at infinity on points of order `q`.
  | _, _ => Fp12.one

/-- `w^(2 (p - 1))` as an element of `Fp2`: `(9 + i)^((p - 1) / 3)`, since `w^6 = 9 + i`. -/
def frobeniusX : Fp2 := Fp2.powNat ⟨9, 1⟩ ((Fp.modulus - 1) / 3)

/-- `w^(3 (p - 1))` as an element of `Fp2`: `(9 + i)^((p - 1) / 2)`. -/
def frobeniusY : Fp2 := Fp2.powNat ⟨9, 1⟩ ((Fp.modulus - 1) / 2)

/-- The `p`-th power of a twisted point, written back on the twist.

`(x w^2)^p = x^p w^(2 p)`, and `x^p` is the conjugate of `x`. -/
def frobenius : Point2 → Point2
  | .infinity => .infinity
  | .affine x y => .affine (x.conj * frobeniusX) (y.conj * frobeniusY)

/-- The Miller loop of the optimal ate pairing, before the final exponentiation.

It follows lines 1 to 13 of Algorithm 1 of [Beuchat et al.](https://eprint.iacr.org/2010/354), §2.

Their `t` is the BN parameter `u`.

It takes `Q` of `G_2` on the twist, and `P = (xp, yp)` of `G_1`. -/
def millerLoop (q : Point2) (xp yp : Fp) : Fp12 :=
  -- The loop adds and doubles points on the twist, over `Fp2`.
  --
  -- Line 1: write `s = 6t + 2` as `s = sum_{i=0}^{L-1} s_i 2^i`, with `s_i` in `{-1, 0, 1}`.
  --
  -- The digits here are the bits of `s`, so no `s_i` is `-1`, and lines 5 and 6 never apply.
  --
  -- `s` has `L = 65` bits.
  --
  -- Line 2: `T <- Q, f <- 1`, the start of the fold.
  let (f, r) := (List.range (LOG_ATE_LOOP_COUNT + 1)).foldl (fun (f, r) step =>
    -- Line 3: for `i = L - 2` to 0, so `i` runs from 63 down to 0.
    let i := LOG_ATE_LOOP_COUNT - step
    -- Line 4: `f <- f^2 * l_{T,T}(P); T <- 2T`.
    let f := f * f * linefunc r r xp yp
    let r := r + r
    -- Lines 7 and 8: if `s_i = 1`, then `f <- f * l_{T,Q}(P); T <- T + Q`.
    if ATE_LOOP_COUNT / 2 ^ i % 2 = 1 then (f * linefunc r q xp yp, r + q) else (f, r)) (Fp12.one, q)
  -- Line 11: `Q1 <- pi_p(Q); Q2 <- pi_p^2(Q)`.
  --
  -- Line 13 reads only `-Q2`, so the negation is taken here.
  let q1 := frobenius q
  let nq2 := -frobenius q1
  -- Line 12: `f <- f * l_{T,Q1}(P); T <- T + Q1`.
  --
  -- Its `T <- T + Q1` is computed once, inside line 13.
  let f := f * linefunc r q1 xp yp
  -- Line 13: `f <- f * l_{T,-Q2}(P)`.
  --
  -- Its `T <- T - Q2` is not computed, since no later line reads `T`.
  f * linefunc (r + q1) nq2 xp yp

/-- The final exponent `(p^12 - 1) / q`. -/
def FINAL_EXPONENT : Nat := (Fp.modulus ^ 12 - 1) / Fr.modulus

/-- The BN parameter `u`, with `p = 36 u^4 + 36 u^3 + 24 u^2 + 6 u + 1`. -/
def BN_U : Nat := 4965661367192848881

/-- `f^((p^12 - 1) / q)`, the final exponentiation.

It follows §3 and §5 of [Scott et al.](https://eprint.iacr.org/2008/490), for the BN curves.

Their `x` is the BN parameter `u`, their `r` is the group order `q`, and their `m` is `f`. -/
def finalExponentiation (f : Fp12) : Fp12 :=
  -- §3: `(p^12 - 1) / r = (p^6 - 1) * (p^2 + 1) * [(p^4 - p^2 + 1) / r]`.
  --
  -- §3: the first part, `m^(p^6 - 1)`, by the Frobenius map and one division in `Fp12`.
  let f := Fp12.frobeniusPow 6 f * f.inverse
  -- §3: the second part, `m^(p^2 + 1)`, by the Frobenius map and one product.
  let f := Fp12.frobeniusPow 2 f * f
  -- §5: `m^x`, `m^(x^2) = (m^x)^x` and `m^(x^3) = (m^(x^2))^x`.
  --
  -- `u` is below `2^64`, so 64 bits of square and multiply reach it.
  let fu := Fp12.powBits 64 f BN_U
  let fu2 := Fp12.powBits 64 fu BN_U
  let fu3 := Fp12.powBits 64 fu2 BN_U
  -- §3: after the first part, the element is unitary, so an inversion is a conjugation.
  --
  -- The conjugation is the power `p^6`, since `m^(p^6) = m^(-1)` for a unitary `m`.
  let conj := Fp12.frobeniusPow 6
  -- §5: the hard part is `(p^4 - p^2 + 1) / r = lambda3 p^3 + lambda2 p^2 + lambda1 p + lambda0`.
  --
  -- §3: its power is `(m^(p^3))^lambda3 * (m^(p^2))^lambda2 * (m^p)^lambda1 * m^lambda0`.
  --
  -- The coefficients in the digits are at most 36, below `2^6`.
  let small (a : Fp12) (e : Nat) := Fp12.powBits 6 a e
  -- §5: `m^lambda0`, with `lambda0(x) = -36 x^3 - 30 x^2 - 18 x - 2`.
  let y0 := conj (small fu3 36 * small fu2 30 * small fu 18 * small f 2)
  -- §5: `m^lambda1`, with `lambda1(x) = -36 x^3 - 18 x^2 - 12 x + 1`.
  let y1 := conj (small fu3 36 * small fu2 18 * small fu 12) * f
  -- §5: `m^lambda2`, with `lambda2(x) = 6 x^2 + 1`.
  let y2 := small fu2 6 * f
  -- §5 gives `lambda3 = 1`, and each power by `p^i` is taken after the power by `lambda_i`.
  --
  -- §5 then groups the terms and evaluates them by an addition chain.
  --
  -- Here each digit is raised on its own instead, which gives the same element.
  y0 * Fp12.frobenius y1 * Fp12.frobeniusPow 2 y2 * Fp12.frobeniusPow 3 f

/-- The pairing `e(P, Q)` of a point of `G_1` and a point of `G_2`, an element of `Fp12`.

It is the final exponentiation of the Miller loop.

It is line 14 of Algorithm 1 of [Beuchat et al.](https://eprint.iacr.org/2010/354), §2.

Their `r` is the group order `q`.

A point at infinity gives 1. -/
def pairing : Point → Point2 → Fp12
  -- Line 14: `f <- f^((p^12 - 1) / r)`.
  | .affine xp yp, q@(.affine _ _) => finalExponentiation (millerLoop q xp yp)
  | _, _ => Fp12.one

/-- Whether the product of the pairings of the pairs is 1.

A pair with a point at infinity contributes 1. -/
def pairingCheck (pairs : List (Point × Point2)) : Bool :=
  -- The Miller loops are multiplied, and the product is raised to the final exponent once.
  --
  -- That is valid since `(a * b)^e = a^e * b^e`.
  let product := pairs.foldl (fun f pair =>
    match pair with
    | (.affine xp yp, q@(.affine _ _)) => f * millerLoop q xp yp
    | _ => f) Fp12.one
  -- A product of 1 passes at once, since `1^e = 1`, as when no pair has a Miller loop.
  product == Fp12.one || finalExponentiation product == Fp12.one

end EthLib.Cryptography.AltBn128
