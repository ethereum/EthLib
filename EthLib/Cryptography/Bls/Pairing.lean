module

public import EthLib.Cryptography.Bls.G1
public import EthLib.Cryptography.Bls.G2
public import EthLib.Cryptography.Bls.Fp12

/-!
# `Pairing`

The optimal ate pairing of BLS12-381: `e(P, Q) = Miller(|x|, Q', P)^((p^12 - 1) / r)`.

- `x = -0xd201000000010000` is the BLS parameter, which is negative.
- `P` is in `G1`, and `Q` is in `G2`.
- `Q'` is the untwisted image of `Q` on `E` over `Fp12`.

The Miller loop walks the bits of `|x|` with a point `R` that starts at `Q'`.

At each bit it doubles `R`, and multiplies the product by the tangent line at `P`.

On a set bit it also adds `Q'` to `R`, and multiplies by the line through them at `P`.

Since `x` is negative, the result is then conjugated.

The final exponentiation sends the result to the `r`-th roots of unity in `Fp12`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

/-! ## Miller loop

The loop keeps the point `T` on the twist, in Jacobian coordinates over `Fp2`.

So it divides nothing.

The untwist sends `(x, y)` to `(x w^(-2), y w^(-3))`.

A line through untwisted points, at `P = (xp, yp)`, is `(yp - y w^(-3)) - λ w^(-1) (xp - x w^(-2))`.

Here `λ` is the slope on the twist.

The loop multiplies each line by `w^3` and by a denominator in `Fp2`.

The line becomes `(λ x - y) - λ xp w^2 + yp w^3`, with three coefficients in `Fp2`.

The factor is `c w^3`, with `c` in `Fp2`.

The final exponentiation sends it to 1 when `c` is not zero.
-/

/-- The element `c0 + c2 w^2 + c3 w^3` of `Fp12`. -/
def lineValue (c0 c2 c3 : Fp2) : Fp12 :=
  ⟨⟨c0, c2, Fp2.zero⟩, ⟨Fp2.zero, c3, Fp2.zero⟩⟩

/-- Doubling step: `(T, f) ↦ (2T, f^2 l)`, with `l` the tangent at `T`, at `(xp, yp)`.

With `T = (X, Y, Z)`, the slope is `λ = 3 X^2 / (2 Y Z)`.

The line is multiplied by `2 Y Z^3`: `(3 X^3 - 2 Y^2) - 3 X^2 Z^2 xp w^2 + 2 Y Z^3 yp w^3`. -/
def millerDouble (T : G2) (xp yp : Fp) (f : Fp12) : G2 × Fp12 :=
  let two := Fp2.ofFp (Fp.ofNat 2)
  let three := Fp2.ofFp (Fp.ofNat 3)
  let xx := T.x * T.x
  let zz := T.z * T.z
  let c0 := three * xx * T.x - two * (T.y * T.y)
  let c2 := -(three * xx * zz * Fp2.ofFp xp)
  let c3 := two * T.y * zz * T.z * Fp2.ofFp yp
  (T.double, f * f * lineValue c0 c2 c3)

/-- Addition step: `(T, f) ↦ (T + Q, f l)`, with `l` the line through `T` and `Q = (xq, yq)`.

With `N = yq Z^3 - Y` and `D = (xq Z^2 - X) Z`, the slope is `λ = N / D`.

The line, written through `Q`, is multiplied by `D`: `(N xq - D yq) - N xp w^2 + D yp w^3`. -/
def millerAdd (T : G2) (xq yq : Fp2) (xp yp : Fp) (f : Fp12) : G2 × Fp12 :=
  let zz := T.z * T.z
  let n := yq * zz * T.z - T.y
  let d := (xq * zz - T.x) * T.z
  let c0 := n * xq - d * yq
  let c2 := -(n * Fp2.ofFp xp)
  let c3 := d * Fp2.ofFp yp
  (T.add ⟨xq, yq, Fp2.one⟩, f * lineValue c0 c2 c3)

/-- Walk bits `n - 1` down to `0` of `s` from `(T, f)`.

At each bit it doubles `T`, then adds `Q` if the bit is set. -/
def millerSteps (s : Nat) (xq yq : Fp2) (xp yp : Fp) : Nat → G2 → Fp12 → Fp12
  | 0, _, f => f
  | n + 1, T, f =>
    let (T, f) := millerDouble T xp yp f
    let (T, f) := if (s >>> n) &&& 1 = 1 then millerAdd T xq yq xp yp f else (T, f)
    millerSteps s xq yq xp yp n T f

/-- The Miller loop of `s`, for the affine points `Q = (xq, yq)` of the twist and `P = (xp, yp)`.

The initial `T = Q` and `f = 1` consume the leading bit of `s`.

So the steps start one bit below it.

`Nat.log2 0 = 0`, so `s = 0` takes no steps. -/
def millerLoop (s : Nat) (q : Fp2 × Fp2) (p : Fp × Fp) : Fp12 :=
  millerSteps s q.1 q.2 p.1 p.2 s.log2 ⟨q.1, q.2, Fp2.one⟩ Fp12.one

/-! ## Final exponentiation -/

/-- The BLS parameter `|x|`. -/
def blsX : Nat := 0xD201000000010000

/-- The exponent `(p¹² − 1) / r`. -/
def finalExpExponent : Nat :=
  (Fp.modulus ^ 12 - 1) / Fr.modulus

/-- Raise `f` to `(p¹² − 1) / r`.

The exponent is the product of `p⁶ − 1`, `p² + 1` and the hard part `h = (p⁴ − p² + 1) / r`.

In this tower, `f^(p⁶)` is the conjugate of `f`.

So the first factor costs one inversion: `f^(p⁶ − 1) = conj(f) · f⁻¹`.

The second factor costs two Frobenius maps and one product.

The result `m` satisfies `m^(p⁶) = m⁻¹`.

So the power of `m` by `−n` is the conjugate of its power by `n`.

The hard part uses the BLS parameter `x = −|x|`, since `p` and `r` are polynomials in `x`.

It equals `((|x| + 1)² / 3) (p − |x|) (|x|² + p² − 1) + 1`.

So `m^h` needs only powers by `|x|` and `(|x| + 1) / 3`, Frobenius maps and conjugates.

These exponents have at most 64 bits.

The steps compute exactly `f^((p¹² − 1) / r)`, and a theorem proves it. -/
def finalExponentiation (f : Fp12) : Fp12 :=
  let t := f.conjugate * f.inverse
  let m := t.frobenius.frobenius * t
  -- `a = m^((|x| + 1)² / 3)`.
  let a := (m.powNat ((blsX + 1) / 3)).powNat (blsX + 1)
  -- `b = a^(p − |x|)`.
  let b := a.frobenius * (a.powNat blsX).conjugate
  -- `c = b^(|x|² + p² − 1)`.
  let c := (b.powNat blsX).powNat blsX * b.frobenius.frobenius * b.conjugate
  c * m

/-! ## The pairing -/

/-- Returns `true` iff `∏ e(P_i, Q_i) = 1`. -/
def pairingCheck (pairs : Array (G1 × G2)) : Bool := Id.run do
  let mut acc : Fp12 := Fp12.one
  for (p, q) in pairs do
    -- Identity pairs contribute 1.
    if p.isInfinity || q.isInfinity then continue
    let f := millerLoop blsX q.toAffine p.toAffine
    acc := acc * f.conjugate
  return (finalExponentiation acc).isOne

end EthLib.Cryptography.Bls
