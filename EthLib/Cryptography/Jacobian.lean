module

public import EthLib.Cryptography.Inverse

/-!
# Jacobian coordinates

A point `(x, y)` of the curve `y^2 = x^3 + a x + b` has the Jacobian forms `(X, Y, Z)`.

They satisfy `x = X / Z^2` and `y = Y / Z^3`, for any `Z != 0`.

A form with `Z = 0` is the point at infinity.

Addition and doubling then need no inverse.

Only the conversion back to `(x, y)` inverts, once.

The coordinate formulas are shared with `Coords`, which accepts another field representation.

secp256k1 uses Montgomery limbs for these formulas.

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

/-- Three Jacobian coordinates in a field representation. -/
structure Coords (F : Type) where
  /-- `X`, which is `x Z^2`. -/
  x : F
  /-- `Y`, which is `y Z^3`. -/
  y : F
  /-- `Z`, which is `0` at the point at infinity. -/
  z : F

/-- Read the three modular coordinates as field coordinates. -/
@[inline] abbrev toCoords {m : Nat} (p : Jacobian m) : Coords (Fin m) :=
  ⟨p.x, p.y, p.z⟩

/-- Make a modular Jacobian form from its three field coordinates. -/
@[inline] abbrev ofCoords {m : Nat} (p : Coords (Fin m)) : Jacobian m :=
  ⟨p.x, p.y, p.z⟩

namespace Coords

variable {F : Type} [OfNat F 0] [OfNat F 1]
  [Add F] [Sub F] [Mul F] [DecidableEq F]

/-- Apply a change of field representation to each coordinate. -/
@[inline] def map {F G : Type} (f : F → G) (p : Coords F) : Coords G :=
  ⟨f p.x, f p.y, f p.z⟩

/-- The point at infinity. -/
@[inline] def infinity : Coords F := ⟨1, 1, 0⟩

/-- The point `(x, y)` of a form, or nothing at infinity.

This is the only inverse. -/
@[reducible] def toAffine (inverse : F → F) (p : Coords F) : Option (F × F) :=
  if p.z = 0 then none
  else
    let zi := inverse p.z
    let zi2 := zi * zi
    some (p.x * zi2, p.y * zi2 * zi)

/-- The sum of `n` copies of a field element, using the binary expansion of `n`. -/
@[specialize n] def scale {F : Type} [OfNat F 0] [Add F] (n : Nat) (x : F) : F :=
  if n = 0 then 0
  else if n = 1 then x
  else
    let half := scale (n / 2) x
    let two := half + half
    if n % 2 = 0 then two else two + x
termination_by n
decreasing_by omega

/-- `2 P`, by formula (6) of Cohen, Miyaji and Ono, with the curve's `a`.

At a point with `y = 0`, the result has `Z = 0`, the point at infinity. -/
@[specialize] def double (a : F) (p : Coords F) : Coords F :=
  let xx := p.x * p.x
  let yy := p.y * p.y
  let s := scale 4 (p.x * yy)
  let l := if a = 0 then scale 3 xx else
    let zz := p.z * p.z
    scale 3 xx + a * zz * zz
  let t := l * l - scale 2 s
  ⟨t, l * (s - t) - scale 8 (yy * yy), scale 2 (p.y * p.z)⟩

/-- `P + Q`, by formula (5) of Cohen, Miyaji and Ono, with the curve's `a`.

The formula fails when `P` or `Q` is at infinity, or when both have one `x`.

So those cases come first: the other point, then `2 P` or the point at infinity. -/
@[specialize] def add (a : F) (p q : Coords F) : Coords F :=
  if p.z = 0 then q
  else if q.z = 0 then p
  else
    let z1z1 := p.z * p.z
    let (u1, s1, z1z2) := if q.z = 1 then (p.x, p.y, p.z) else
      let z2z2 := q.z * q.z
      (p.x * z2z2, p.y * q.z * z2z2, p.z * q.z)
    let u2 := q.x * z1z1
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
      let x3 := r * r - hhh - scale 2 v
      ⟨x3, r * (v - x3) - s1 * hhh, z1z2 * h⟩

/-- `k P`, for `k < 2^fuel`, by double and add on the bits of `k`, low bit first.

It recurses on `fuel`, so the kernel can run it. -/
@[specialize, reducible] def mulBits (a : F) : Nat → Nat → Coords F → Coords F
  | 0, _, _ => infinity
  | fuel + 1, k, p =>
    -- `k P = (k mod 2) P + (k / 2) (2 P)`.
    let rest := mulBits a fuel (k / 2) (double a p)
    if k % 2 = 1 then add a p rest else rest

/-- `k P + l Q`, for `k, l < 2^fuel`, with one chain of doublings for both, high bits first.

`pq` is `P + Q`, which each pair of bits that are both `1` adds at once.

It recurses on `fuel`, so the kernel can run it. -/
@[specialize, reducible] def mulAddAux (a : F) (p q pq : Coords F) : Nat → Nat → Nat → Coords F
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
@[specialize, reducible] def mulAdd (a : F) (fuel k : Nat) (p : Coords F) (l : Nat)
    (q : Coords F) : Coords F :=
  mulAddAux a p q (add a p q) fuel k l

end Coords

variable {m : Nat} [NeZero m]

/-- The point at infinity. -/
@[inline, reducible] def infinity : Jacobian m := ofCoords Coords.infinity

/-- The Jacobian form `(x, y, 1)` of the point `(x, y)`. -/
def ofAffine (x y : Fin m) : Jacobian m := ⟨x, y, 1⟩

/-- The point `(x, y)` of a form, or nothing at infinity.

This is the only inverse. -/
@[inline, reducible] def toAffine (p : Jacobian m) : Option (Fin m × Fin m) :=
  Coords.toAffine Fin.inverse p.toCoords

/-- `2 P`, by formula (6) of Cohen, Miyaji and Ono, with the curve's `a`.

At a point with `y = 0`, the result has `Z = 0`, the point at infinity. -/
@[inline, reducible] def double (a : Fin m) (p : Jacobian m) : Jacobian m :=
  ofCoords (Coords.double a p.toCoords)

/-- `P + Q`, by formula (5) of Cohen, Miyaji and Ono, with the curve's `a`.

The formula fails when `P` or `Q` is at infinity, or when both have one `x`.

So those cases come first: the other point, then `2 P` or the point at infinity. -/
@[inline, reducible] def add (a : Fin m) (p q : Jacobian m) : Jacobian m :=
  ofCoords (Coords.add a p.toCoords q.toCoords)

/-- `k P`, for `k < 2^fuel`, by double and add on the bits of `k`, low bit first.

It recurses on `fuel`, so the kernel can run it. -/
@[inline, reducible] def mulBits (a : Fin m) (fuel k : Nat) (p : Jacobian m) : Jacobian m :=
  ofCoords (Coords.mulBits a fuel k p.toCoords)

/-- `k P + l Q`, for `k, l < 2^fuel`, with one chain of doublings for both, high bits first.

`pq` is `P + Q`, which each pair of bits that are both `1` adds at once.

It recurses on `fuel`, so the kernel can run it. -/
@[inline, reducible] def mulAddAux (a : Fin m) (p q pq : Jacobian m) (fuel k l : Nat) :
    Jacobian m :=
  ofCoords (Coords.mulAddAux a p.toCoords q.toCoords pq.toCoords fuel k l)

/-- `k P + l Q`, for `k, l < 2^fuel`, by simultaneous multiple point multiplication.

The two products share their doublings: `fuel` doublings in total, instead of `2 fuel`.

The method is Algorithm 3.48, in §3.3.3 of "Guide to Elliptic Curve Cryptography".

Its windows here have one bit.

That book is by Hankerson, Menezes and Vanstone (Springer, 2004). -/
@[inline, reducible] def mulAdd (a : Fin m) (fuel k : Nat) (p : Jacobian m) (l : Nat)
    (q : Jacobian m) : Jacobian m :=
  ofCoords (Coords.mulAdd a fuel k p.toCoords l q.toCoords)

end Jacobian

end EthLib.Cryptography
