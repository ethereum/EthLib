module

public import EthLib.Cryptography.AltBn128.Curve

/-!
# `AltBn128.Pairing`

The optimal ate pairing of alt_bn128, which EIP-197 checks products of.

The pairing maps a point of `G_1` and a point of `G_2` to `Fp12`, and it is bilinear: `e(a P, b Q) = e(P, Q)^(a b)`.

The fields follow py_ecc, the library that execution-specs calls:

- `Fp2 = Fp[i] / (i^2 + 1)`, where the points of `G_2` live.
- `Fp12 = Fp[w] / (w^12 - 18 w^6 + 82)`, where the pairing lands.
- `Fp2` sits inside `Fp12` by `a + b i -> (a - 9 b) + b w^6`, since `(w^6 - 9)^2 = -1` there.

`G_2` lies on the twist `y^2 = x^3 + 3 / (9 + i)` over `Fp2`.

The twist sends `(x, y)` to `(x w^2, y w^3)` on `y^2 = x^3 + 3` over `Fp12`.

The Miller loop adds and doubles points on the twist, over `Fp2`.

Each line of the loop is evaluated in `Fp12`, as py_ecc evaluates it on the twisted points.
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

/-- The product: the product of the polynomials, reduced with `w^12 = 18 w^6 - 82`. -/
def mul (a b : Fp12) : Fp12 :=
  -- The 23 coefficients of the product of the polynomials.
  let product : Array Fp := Array.ofFn (n := 23) fun m =>
    (List.range 12).foldl (fun acc i =>
      if i ≤ m.val ∧ m.val - i < 12 then acc + a[i]! * b[m.val - i]! else acc) 0
  -- From the top degree down, `w^m = 18 w^(m - 6) - 82 w^(m - 12)` folds each high term into lower ones.
  let reduced := (List.range 11).foldl (fun (coefficients : Array Fp) step =>
    let m := 22 - step
    let top := coefficients[m]!
    (coefficients.modify (m - 6) (· + 18 * top)).modify (m - 12) (· - 82 * top)) product
  Vector.ofFn fun k => reduced[k.val]!

instance : Add Fp12 := ⟨add⟩
instance : Sub Fp12 := ⟨sub⟩
instance : Mul Fp12 := ⟨mul⟩

/-- `a^e`, for `e < 2^fuel`, by square and multiply on the bits of `e`. -/
def powBits : Nat → Fp12 → Nat → Fp12
  | 0, _, _ => one
  | fuel + 1, a, e =>
    let half := powBits fuel (a * a) (e / 2)
    if e % 2 = 1 then a * half else half

end Fp12

/-! ## The pairing -/

/-- `ate_loop_count`, the length of the Miller loop in py_ecc. -/
def ATE_LOOP_COUNT : Nat := 29793968203157093288

/-- `log_ate_loop_count`, the index of the top bit that the loop starts from. -/
def LOG_ATE_LOOP_COUNT : Nat := 63

/-- `linefunc`: the line through the twisted points `r` and `q`, at the point `(xt, yt)` of `G_1`.

A twisted point has `x` times `w^2` and `y` times `w^3`.

So a slope `l` of the twist is the slope `l w` of the twisted points.

- Two different `x`: the chord, `l w (xt - x1 w^2) - (yt - y1 w^3)`.
- The same point: the tangent, of the same form.
- Opposite points: the vertical line `xt - x1 w^2`. -/
def linefunc (r q : Point2) (xt yt : Fp) : Fp12 :=
  match r, q with
  | .affine x1 y1, .affine x2 y2 =>
    let w := Fp12.wPow 1
    let w2 := Fp12.wPow 2
    let w3 := Fp12.wPow 3
    let slopeLine (l : Fp2) : Fp12 :=
      Fp12.ofFp2 l * w * (Fp12.ofFp xt - Fp12.ofFp2 x1 * w2) - (Fp12.ofFp yt - Fp12.ofFp2 y1 * w3)
    if x1 ≠ x2 then
      slopeLine ((y2 - y1) * (x2 - x1).inv)
    else if y1 = y2 then
      slopeLine (Fp2.ofFp 3 * x1 * x1 * (Fp2.ofFp 2 * y1).inv)
    else
      Fp12.ofFp xt - Fp12.ofFp2 x1 * w2
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

/-- The Miller loop of `miller_loop` in py_ecc, before the final exponentiation. -/
def millerLoop (q : Point2) (xp yp : Fp) : Fp12 :=
  -- The bits of `ATE_LOOP_COUNT` from the top, each doubling `r`, then adding `q` on a set bit.
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

/-- Whether the product of the pairings of the pairs is 1.

A pair with a point at infinity contributes 1, as in py_ecc.

The Miller loops are multiplied, then raised to the final exponent once, since `(a * b)^e = a^e * b^e`. -/
def pairingCheck (pairs : List (Point × Point2)) : Bool :=
  let product := pairs.foldl (fun f pair =>
    match pair with
    | (.affine xp yp, q@(.affine _ _)) => f * millerLoop q xp yp
    | _ => f) Fp12.one
  -- `FINAL_EXPONENT` has fewer than 3072 bits.
  Fp12.powBits 3072 product FINAL_EXPONENT == Fp12.one

end EthLib.Cryptography.AltBn128
