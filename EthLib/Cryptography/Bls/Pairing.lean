module

public import EthLib.Cryptography.Bls.G1
public import EthLib.Cryptography.Bls.G2
public import EthLib.Cryptography.Bls.Fp12

/-!
# `Pairing`

The optimal ate pairing of BLS12-381: `e(P, Q) = Miller(|x|, Q', P')^((p^12 - 1) / r)`.

- `x = -0xd201000000010000` is the BLS parameter, which is negative.
- `P` is in `G1`, and `Q` is in `G2`.
- `Q'` is the untwisted image of `Q` on `E` over `Fp12`.
- `P'` is `P` on `E` over `Fp12`, by the inclusion of `Fp` in `Fp12`.

The Miller loop walks the bits of `|x|` with a point `R` that starts at `Q'`.

At each bit it doubles `R`, and multiplies the product by the tangent line at `P'`.

On a set bit it also adds `Q'` to `R`, and multiplies by the line through them at `P'`.

Since `x` is negative, the result is then conjugated.

The final exponentiation sends the result to the `r`-th roots of unity in `Fp12`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

/-! ## Embedding G1 and G2 into E(Fp12)

To compute the Miller loop over `Fp12` we lift both groups to a single
ambient curve `E : y² = x³ + 4` over `Fp12`.

* G1's coordinates are already in `Fp ⊂ Fp12`. Just wrap them.
* G2's coordinates live on the twist `E' : y² = x³ + 4·(1+i)` over `Fp2`.
  The untwist isomorphism sends `(X, Y) ↦ (X / w², Y / w³)`, where
  `w ∈ Fp12` is the generator with `w² = v ∈ Fp6` and `v³ = 1+i ∈ Fp2`.
  We compute `w⁻²` and `w⁻³` once at the start of a pairing.
-/

namespace Embedded

/-- An affine point on `E/Fp12`. -/
structure Point where
  x : Fp12
  y : Fp12
  inf : Bool := false
deriving Inhabited

/-- Lift a `G1` point into `E(Fp12)` via the trivial inclusion. -/
def ofG1 (p : G1) : Point :=
  if p.isInfinity then { x := Fp12.zero, y := Fp12.zero, inf := true }
  else
    let (xp, yp) := p.toAffine
    { x := ⟨Fp6.ofFp2 (Fp2.ofFp xp), Fp6.zero⟩
    , y := ⟨Fp6.ofFp2 (Fp2.ofFp yp), Fp6.zero⟩ }

/-- `w⁻² ∈ Fp12`. Since `w² = v ∈ Fp6`, this is `v⁻¹` lifted. -/
def wInv2 : Fp12 :=
  let v : Fp6 := ⟨Fp2.zero, Fp2.one, Fp2.zero⟩
  ⟨v.inverse, Fp6.zero⟩

/-- `w⁻³ ∈ Fp12`, equal to `v⁻²·w` in `⟨c0, c1⟩` form. -/
def wInv3 : Fp12 :=
  let v : Fp6 := ⟨Fp2.zero, Fp2.one, Fp2.zero⟩
  let v2inv := (v * v).inverse
  ⟨Fp6.zero, v2inv⟩

/-- Lift a `G2` point into `E(Fp12)` via the untwist isomorphism
`(X, Y) ↦ (X / w², Y / w³)`. -/
def ofG2 (p : G2) : Point :=
  if p.isInfinity then { x := Fp12.zero, y := Fp12.zero, inf := true }
  else
    let (X, Y) := p.toAffine
    let X12 : Fp12 := ⟨Fp6.ofFp2 X, Fp6.zero⟩
    let Y12 : Fp12 := ⟨Fp6.ofFp2 Y, Fp6.zero⟩
    { x := X12 * wInv2, y := Y12 * wInv3 }

end Embedded

/-! ## Line functions -/

namespace Line

/-- Slope of the line through two distinct points. -/
@[inline] def addSlope (Rx Ry Tx Ty : Fp12) : Fp12 :=
  (Ty - Ry) * (Tx - Rx).inverse

/-- Slope of the tangent at `R`. -/
@[inline] def tangentSlope (Rx Ry : Fp12) : Fp12 :=
  let three : Fp12 := ⟨Fp6.ofFp2 (Fp2.ofFp (Fp.ofNat 3)), Fp6.zero⟩
  let two   : Fp12 := ⟨Fp6.ofFp2 (Fp2.ofFp (Fp.ofNat 2)), Fp6.zero⟩
  three * Rx * Rx * (two * Ry).inverse

/-- Evaluate the line at `(xp, yp)`: `(yp − Ry) − slope·(xp − Rx)`. -/
@[inline] def evalAt (Rx Ry slope xp yp : Fp12) : Fp12 :=
  (yp - Ry) - slope * (xp - Rx)

end Line

/-! ## Miller loop -/

/-- Doubling step: `(T, f) ↦ (2T, f² · l_{T,T}(P))`. -/
def millerDouble (T : Embedded.Point) (P : Embedded.Point) (f : Fp12)
    : Embedded.Point × Fp12 :=
  if T.inf then (T, f * f)
  else
    let m := Line.tangentSlope T.x T.y
    let nx := m * m - T.x - T.x
    let ny := m * (T.x - nx) - T.y
    let line := Line.evalAt T.x T.y m P.x P.y
    ({ x := nx, y := ny, inf := false }, f * f * line)

/-- Addition step: `(T, f) ↦ (T + R₀, f · l_{T,R₀}(P))`. -/
def millerAdd (T R₀ : Embedded.Point) (P : Embedded.Point) (f : Fp12)
    : Embedded.Point × Fp12 :=
  if T.inf then (R₀, f)
  else if R₀.inf then (T, f)
  else
    let m := Line.addSlope T.x T.y R₀.x R₀.y
    let nx := m * m - T.x - R₀.x
    let ny := m * (T.x - nx) - T.y
    let line := Line.evalAt T.x T.y m P.x P.y
    ({ x := nx, y := ny, inf := false }, f * line)

/-- Walk bits `n - 1` down to `0` of `s` from `(T, f)`: double at every
bit, then add `R₀` where the bit is set. -/
def millerSteps (s : Nat) (R₀ P : Embedded.Point) :
    Nat → Embedded.Point → Fp12 → Fp12
  | 0, _, f => f
  | n + 1, T, f =>
    let (T, f) := millerDouble T P f
    let (T, f) := if (s >>> n) &&& 1 = 1 then millerAdd T R₀ P f else (T, f)
    millerSteps s R₀ P n T f

/-- Walk the bits of `s` from the most-significant down. The leading bit
is consumed by the initial `T = R₀` and `f = 1`, so the steps start one
bit below it. `Nat.log2 0 = 0`, so `s = 0` takes no steps. -/
def millerLoop (s : Nat) (R₀ P : Embedded.Point) : Fp12 :=
  millerSteps s R₀ P s.log2 R₀ Fp12.one

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
    let f := millerLoop blsX (Embedded.ofG2 q) (Embedded.ofG1 p)
    acc := acc * f.conjugate
  return (finalExponentiation acc).isOne

end EthLib.Cryptography.Bls
