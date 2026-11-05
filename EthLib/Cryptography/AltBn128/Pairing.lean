module

public import EthLib.Cryptography.AltBn128.Curve

/-!
# `AltBn128.Pairing`

The optimal ate pairing of alt_bn128, which EIP-197 checks products of.

The pairing maps a point of `G_1` and a point of `G_2` to `Fp12`.

It is bilinear: `e(a P, b Q) = e(P, Q)^(a b)`.

It uses two extension fields of `Fp`:

- `Fp2 = Fp[i] / (i^2 + 1)`, where the points of `G_2` live.
- `Fp12 = Fp[w] / (w^12 - 18 w^6 + 82)`, where the pairing lands.
- `Fp2` sits inside `Fp12` by `a + b i -> (a - 9 b) + b w^6`, since `(w^6 - 9)^2 = -1` there.

`G_2` lies on the twist `y^2 = x^3 + 3 / (9 + i)` over `Fp2`.

The twist sends `(x, y)` to `(x w^2, y w^3)` on `y^2 = x^3 + 3` over `Fp12`.

The Miller loop adds and doubles points on the twist, over `Fp2`.

Each line of the loop is evaluated in `Fp12`, at the twisted points.
-/

@[expose] public section

namespace EthLib.Cryptography.AltBn128

/-! ## `Fp2` -/

/-- An element `c0 + c1 i` of `Fp2`. -/
structure Fp2 where
  /-- The coefficient of 1. -/
  c0 : Fp
  /-- The coefficient of `i`. -/
  c1 : Fp
deriving DecidableEq, Repr, Inhabited

namespace Fp2

/-- The sum, coefficient by coefficient. -/
def add (a b : Fp2) : Fp2 := ⟨a.c0 + b.c0, a.c1 + b.c1⟩

/-- The difference, coefficient by coefficient. -/
def sub (a b : Fp2) : Fp2 := ⟨a.c0 - b.c0, a.c1 - b.c1⟩

/-- The product, with `i^2 = -1`. -/
def mul (a b : Fp2) : Fp2 := ⟨a.c0 * b.c0 - a.c1 * b.c1, a.c0 * b.c1 + a.c1 * b.c0⟩

/-- The negative. -/
def neg (a : Fp2) : Fp2 := ⟨-a.c0, -a.c1⟩

/-- The conjugate `c0 - c1 i`, which is also `a^p`. -/
def conj (a : Fp2) : Fp2 := ⟨a.c0, -a.c1⟩

/-- The inverse: `(c0 - c1 i) / (c0^2 + c1^2)`, and 0 for 0. -/
def inv (a : Fp2) : Fp2 :=
  let norm := (a.c0 * a.c0 + a.c1 * a.c1).inv
  ⟨a.c0 * norm, -(a.c1 * norm)⟩

instance : Add Fp2 := ⟨add⟩
instance : Sub Fp2 := ⟨sub⟩
instance : Mul Fp2 := ⟨mul⟩
instance : Neg Fp2 := ⟨neg⟩

/-- The element of `Fp`. -/
def ofFp (a : Fp) : Fp2 := ⟨a, 0⟩

/-- `a^e`, for `e < 2^fuel`, by square and multiply on the bits of `e`. -/
def powBits : Nat → Fp2 → Nat → Fp2
  | 0, _, _ => ⟨1, 0⟩
  | fuel + 1, a, e =>
    let half := powBits fuel (a * a) (e / 2)
    if e % 2 = 1 then a * half else half

end Fp2

/-! ## The twist and `G_2` -/

/-- `b2 = 3 / (9 + i)`, the constant of the twist, from EIP-197. -/
def b2 : Fp2 := Fp2.mul (Fp2.ofFp 3) (Fp2.inv ⟨9, 1⟩)

/-- A point of the twist over `Fp2`, or the point at infinity. -/
inductive Point2 where
  /-- The point at infinity, the zero of the group. -/
  | infinity
  /-- The point `(x, y)`. -/
  | affine (x y : Fp2)
deriving DecidableEq, Repr, Inhabited

namespace Point2

/-- Whether a point satisfies `y^2 = x^3 + b2`. -/
def isOnCurve : Point2 → Bool
  | infinity => true
  | affine x y => y * y == x * x * x + b2

/-- The generator `P2` of `G_2`, from EIP-197 §"Definition of the groups".

EIP-197 writes each coordinate as `c1 i + c0`. -/
def generator : Point2 :=
  affine
    ⟨10857046999023057135944570762232829481370756359578518086990519993285655852781,
      11559732032986387107991004021392285783925812861821192530917403151452391805634⟩
    ⟨8495653923123431417604973247489272438418190587263600148770280649306958101930,
      4082367875863433681332203403145435568316851327593401208105741076214120093531⟩

/-- The sum of two points, by the same rule as on `G_1`, over `Fp2`. -/
def add : Point2 → Point2 → Point2
  | infinity, q => q
  | p, infinity => p
  | affine x1 y1, affine x2 y2 =>
    if x1 = x2 then
      if y2 = -y1 then infinity
      else
        -- The point is doubled, with the tangent's slope.
        let l := Fp2.ofFp 3 * x1 * x1 * (Fp2.ofFp 2 * y1).inv
        let x3 := l * l - x1 - x2
        affine x3 (l * (x1 - x3) - y1)
    else
      -- Two different x: the chord's slope.
      let l := (y2 - y1) * (x2 - x1).inv
      let x3 := l * l - x1 - x2
      affine x3 (l * (x1 - x3) - y1)

instance : Add Point2 := ⟨add⟩

/-- `k P`, for `k < 2^fuel`, by double and add on the bits of `k`. -/
def mulBits : Nat → Nat → Point2 → Point2
  | 0, _, _ => infinity
  | fuel + 1, k, p =>
    let rest := mulBits fuel (k / 2) (p + p)
    if k % 2 = 1 then p + rest else rest

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

The coefficient of `w^m` in the product of the polynomials is `c_m`, for `m ≤ 22`.

Each `w^m` with `m ≥ 12` is `18 w^(m - 6) - 82 w^(m - 12)`.

So the terms of `w^18` to `w^22` first fold into those of `w^12` to `w^16`.

The sums are taken on the values in `Nat`, and each coefficient is reduced modulo `p` once. -/
def mul (a b : Fp12) : Fp12 :=
  let x0 := a[0].val; let x1 := a[1].val; let x2 := a[2].val; let x3 := a[3].val
  let x4 := a[4].val; let x5 := a[5].val; let x6 := a[6].val; let x7 := a[7].val
  let x8 := a[8].val; let x9 := a[9].val; let x10 := a[10].val; let x11 := a[11].val
  let y0 := b[0].val; let y1 := b[1].val; let y2 := b[2].val; let y3 := b[3].val
  let y4 := b[4].val; let y5 := b[5].val; let y6 := b[6].val; let y7 := b[7].val
  let y8 := b[8].val; let y9 := b[9].val; let y10 := b[10].val; let y11 := b[11].val
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
def frobeniusGamma : Fp2 := Fp2.powBits 256 ⟨9, 1⟩ ((Fp.modulus - 1) / 6)

/-- The powers `(w^p)^k` for `k < 12`, which are also `(w^k)^p`.

`6` divides `p - 1`, so `w^p = w (w^6)^((p - 1) / 6)` is `w` times an element of `Fp2`. -/
def frobeniusCoefficients : Array Fp12 :=
  let wp := wPow 1 * ofFp2 frobeniusGamma
  (List.range 11).foldl (fun powers _ => powers.push (powers.back! * wp)) #[one]

/-- The `p`-th power.

Each coefficient `a_k` lies in `Fp`, so `a_k^p = a_k`.

So `(sum_k a_k w^k)^p = sum_k a_k (w^p)^k`. -/
def frobenius (a : Fp12) : Fp12 :=
  (List.range 12).foldl (fun acc k => acc + scale a[k]! frobeniusCoefficients[k]!) (ofFp 0)

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

It is `l w (xt - x1 w^2) - (yt - y1 w^3)`.

An element `a + b i` of `Fp2` is `(a - 9 b) + b w^6` in `Fp12`, so the line has a closed form.

Write `l = l0 + l1 i` and `y1 - l x1 = d0 + d1 i`.

Then the line is `-yt + xt (l0 - 9 l1) w + (d0 - 9 d1) w^3 + xt l1 w^7 + d1 w^9`. -/
def slopeLine (l x1 y1 : Fp2) (xt yt : Fp) : Fp12 :=
  let d := y1 - l * x1
  #v[-yt, xt * (l.c0 - 9 * l.c1), 0, d.c0 - 9 * d.c1, 0, 0, 0, xt * l.c1, 0, d.c1, 0, 0]

/-- The vertical line `xt - x1 w^2` through the twisted point with `x` coordinate `x1 w^2`.

With `x1 = a + b i`, it is `xt - (a - 9 b) w^2 - b w^8`. -/
def verticalLine (x1 : Fp2) (xt : Fp) : Fp12 :=
  #v[xt, 0, -(x1.c0 - 9 * x1.c1), 0, 0, 0, 0, 0, -x1.c1, 0, 0, 0]

/-- The line through the twisted points `r` and `q`, at the point `(xt, yt)` of `G_1`.

A twisted point has `x` times `w^2` and `y` times `w^3`.

So a slope `l` of the twist is the slope `l w` of the twisted points.

- Two different `x`: the chord.
- The same point: the tangent.
- Opposite points: the vertical line. -/
def linefunc (r q : Point2) (xt yt : Fp) : Fp12 :=
  match r, q with
  | .affine x1 y1, .affine x2 y2 =>
    if x1 ≠ x2 then
      slopeLine ((y2 - y1) * (x2 - x1).inv) x1 y1 xt yt
    else if y1 = y2 then
      slopeLine (Fp2.ofFp 3 * x1 * x1 * (Fp2.ofFp 2 * y1).inv) x1 y1 xt yt
    else
      verticalLine x1 xt
  -- The loop never meets the point at infinity on points of order `q`.
  | _, _ => Fp12.one

/-- `w^(2 (p - 1))` as an element of `Fp2`: `(9 + i)^((p - 1) / 3)`, since `w^6 = 9 + i`. -/
def frobeniusX : Fp2 := Fp2.powBits 256 ⟨9, 1⟩ ((Fp.modulus - 1) / 3)

/-- `w^(3 (p - 1))` as an element of `Fp2`: `(9 + i)^((p - 1) / 2)`. -/
def frobeniusY : Fp2 := Fp2.powBits 256 ⟨9, 1⟩ ((Fp.modulus - 1) / 2)

/-- The `p`-th power of a twisted point, written back on the twist.

`(x w^2)^p = x^p w^(2 p)`, and `x^p` is the conjugate of `x`. -/
def frobenius : Point2 → Point2
  | .infinity => .infinity
  | .affine x y => .affine (x.conj * frobeniusX) (y.conj * frobeniusY)

/-- The Miller loop of the optimal ate pairing, before the final exponentiation. -/
def millerLoop (q : Point2) (xp yp : Fp) : Fp12 :=
  -- The bits below the top one, each doubling `r`, then adding `q` on a set bit.
  let (f, r) := (List.range (LOG_ATE_LOOP_COUNT + 1)).foldl (fun (f, r) step =>
    let i := LOG_ATE_LOOP_COUNT - step
    let f := f * f * linefunc r r xp yp
    let r := r + r
    if ATE_LOOP_COUNT / 2 ^ i % 2 = 1 then (f * linefunc r q xp yp, r + q) else (f, r)) (Fp12.one, q)
  -- Two more lines, through the `p`-th and the negated `p^2`-th powers of `q`.
  let q1 := frobenius q
  let nq2 := match frobenius q1 with
    | .affine x y => Point2.affine x (-y)
    | .infinity => .infinity
  let f := f * linefunc r q1 xp yp
  f * linefunc (r + q1) nq2 xp yp

/-- The final exponent `(p^12 - 1) / q`. -/
def FINAL_EXPONENT : Nat := (Fp.modulus ^ 12 - 1) / Fr.modulus

/-- The BN parameter `u`, with `p = 36 u^4 + 36 u^3 + 24 u^2 + 6 u + 1`. -/
def BN_U : Nat := 4965661367192848881

/-- `f^((p^12 - 1) / q)`, the final exponentiation.

[Scott et al.](https://eprint.iacr.org/2008/490), §3, split the exponent.

It is `(p^6 - 1) (p^2 + 1) (p^4 - p^2 + 1) / q`.

The first two factors cost a few Frobenius maps and one inverse.

After them, `f^(p^6) = f^(-1)`, so a power by a negative number is a power of the conjugate.

Their §5 writes `(p^4 - p^2 + 1) / q` in base `p`, with digits `l0` to `l3` in `u`.

- `l3 = 1` and `l2 = 6 u^2 + 1`.
- `l1 = -36 u^3 - 18 u^2 - 12 u + 1`.
- `l0 = -36 u^3 - 30 u^2 - 18 u - 2`.

So the last factor needs three powers by `u` and a few by small numbers. -/
def finalExponentiation (f : Fp12) : Fp12 :=
  -- `f^((p^6 - 1) (p^2 + 1))`.
  let f := Fp12.frobeniusPow 6 f * f.inverse
  let f := Fp12.frobeniusPow 2 f * f
  -- `f^u`, `f^(u^2)` and `f^(u^3)`, each below `2^64`.
  let fu := Fp12.powBits 64 f BN_U
  let fu2 := Fp12.powBits 64 fu BN_U
  let fu3 := Fp12.powBits 64 fu2 BN_U
  -- The four digits, with the conjugate for each negative part.
  let conj := Fp12.frobeniusPow 6
  let small (a : Fp12) (e : Nat) := Fp12.powBits 6 a e
  let y0 := conj (small fu3 36 * small fu2 30 * small fu 18 * small f 2)
  let y1 := conj (small fu3 36 * small fu2 18 * small fu 12) * f
  let y2 := small fu2 6 * f
  y0 * Fp12.frobenius y1 * Fp12.frobeniusPow 2 y2 * Fp12.frobeniusPow 3 f

/-- The pairing `e(P, Q)` of a point of `G_1` and a point of `G_2`, an element of `Fp12`.

It is the final exponentiation of the Miller loop.

A point at infinity gives 1. -/
def pairing : Point → Point2 → Fp12
  | .affine xp yp, q@(.affine _ _) => finalExponentiation (millerLoop q xp yp)
  | _, _ => Fp12.one

/-- Whether the product of the pairings of the pairs is 1.

A pair with a point at infinity contributes 1.

The Miller loops are multiplied, then raised to the final exponent once.

That is valid since `(a * b)^e = a^e * b^e`. -/
def pairingCheck (pairs : List (Point × Point2)) : Bool :=
  let product := pairs.foldl (fun f pair =>
    match pair with
    | (.affine xp yp, q@(.affine _ _)) => f * millerLoop q xp yp
    | _ => f) Fp12.one
  finalExponentiation product == Fp12.one

end EthLib.Cryptography.AltBn128
