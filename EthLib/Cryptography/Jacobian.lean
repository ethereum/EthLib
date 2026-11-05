module

public import EthLib.Cryptography.Inverse

/-!
# Jacobian coordinates

A point `(x, y)` of the curve `y^2 = x^3 + a x + b` has the Jacobian forms `(X, Y, Z)`.

They satisfy `x = X / Z^2` and `y = Y / Z^3`, for any `Z != 0`.

A form with `Z = 0` is the point at infinity.

Addition and doubling then need no inverse.

Only the conversion back to `(x, y)` inverts, once.

The formulas are those of Cohen, Miyaji and Ono (1998), formulas (5) and (6).

The Explicit-Formulas Database lists them as add-1998-cmo-2 and dbl-1998-cmo-2:
<https://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html>.
-/

@[expose] public section

namespace EthLib.Cryptography

/-- A point in Jacobian coordinates over the integers mod `m`. -/
structure Jacobian (m : Nat) where
  /-- `X`, which is `x Z^2`. -/
  x : Fin m
  /-- `Y`, which is `y Z^3`. -/
  y : Fin m
  /-- `Z`, which is `0` at the point at infinity. -/
  z : Fin m

namespace Jacobian

variable {m : Nat} [NeZero m]

/-- The point at infinity. -/
def infinity : Jacobian m := ⟨1, 1, 0⟩

/-- The Jacobian form `(x, y, 1)` of the point `(x, y)`. -/
def ofAffine (x y : Fin m) : Jacobian m := ⟨x, y, 1⟩

/-- The point `(x, y)` of a form, or nothing at infinity.

This is the only inverse. -/
def toAffine (p : Jacobian m) : Option (Fin m × Fin m) :=
  if p.z = 0 then none
  else
    let zi := Fin.inverse p.z
    let zi2 := zi * zi
    some (p.x * zi2, p.y * zi2 * zi)

/-- `2 P`, by formula (6) of Cohen, Miyaji and Ono, with the curve's `a`.

At a point with `y = 0`, the result has `Z = 0`, the point at infinity. -/
def double (a : Fin m) (p : Jacobian m) : Jacobian m :=
  let xx := p.x * p.x
  let yy := p.y * p.y
  let zz := p.z * p.z
  let s := 4 * p.x * yy
  let l := 3 * xx + a * zz * zz
  let t := l * l - 2 * s
  ⟨t, l * (s - t) - 8 * yy * yy, 2 * p.y * p.z⟩

/-- `P + Q`, by formula (5) of Cohen, Miyaji and Ono, with the curve's `a`.

The formula fails when `P` or `Q` is at infinity, or when both have one `x`.

So those cases come first: the other point, then `2 P` or the point at infinity. -/
def add (a : Fin m) (p q : Jacobian m) : Jacobian m :=
  if p.z = 0 then q
  else if q.z = 0 then p
  else
    let z1z1 := p.z * p.z
    let z2z2 := q.z * q.z
    let u1 := p.x * z2z2
    let u2 := q.x * z1z1
    let s1 := p.y * q.z * z2z2
    let s2 := q.y * p.z * z1z1
    let h := u2 - u1
    let r := s2 - s1
    if h = 0 then
      -- One `x`: the same point, or opposite points.
      if r = 0 then double a p else infinity
    else
      let hh := h * h
      let hhh := h * hh
      let v := u1 * hh
      let x3 := r * r - hhh - 2 * v
      ⟨x3, r * (v - x3) - s1 * hhh, p.z * q.z * h⟩

/-- `k P`, for `k < 2^fuel`, by double and add on the bits of `k`, low bit first.

It recurses on `fuel`, so the kernel can run it. -/
def mulBits (a : Fin m) : Nat → Nat → Jacobian m → Jacobian m
  | 0, _, _ => infinity
  | fuel + 1, k, p =>
    -- `k P = (k mod 2) P + (k / 2) (2 P)`.
    let rest := mulBits a fuel (k / 2) (double a p)
    if k % 2 = 1 then add a p rest else rest

/-- `k P + l Q`, for `k, l < 2^fuel`, with one chain of doublings for both, high bits first.

`pq` is `P + Q`, which each pair of bits that are both `1` adds at once.

It recurses on `fuel`, so the kernel can run it. -/
def mulAddAux (a : Fin m) (p q pq : Jacobian m) : Nat → Nat → Nat → Jacobian m
  | 0, _, _ => infinity
  | fuel + 1, k, l =>
    -- `k P + l Q = 2 ((k / 2) P + (l / 2) Q) + (k mod 2) P + (l mod 2) Q`.
    let acc := double a (mulAddAux a p q pq fuel (k / 2) (l / 2))
    if k % 2 = 1 then
      if l % 2 = 1 then add a acc pq else add a acc p
    else if l % 2 = 1 then add a acc q else acc

/-- `k P + l Q`, for `k, l < 2^fuel`, by simultaneous multiple point multiplication.

The two products share their doublings: `fuel` doublings in total, instead of `2 fuel`.

The method is Algorithm 3.48, in §3.3.3 of "Guide to Elliptic Curve Cryptography".

Its windows here have one bit.

That book is by Hankerson, Menezes and Vanstone (Springer, 2004). -/
def mulAdd (a : Fin m) (fuel k : Nat) (p : Jacobian m) (l : Nat) (q : Jacobian m) : Jacobian m :=
  mulAddAux a p q (add a p q) fuel k l

end Jacobian

end EthLib.Cryptography
