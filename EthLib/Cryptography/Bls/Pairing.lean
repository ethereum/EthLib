module

public import EthLib.Cryptography.Bls.G1
public import EthLib.Cryptography.Bls.G2
public import EthLib.Cryptography.Bls.Fp12

/-!
# `Pairing`

The optimal ate pairing of BLS12-381: `e(P, Q) = conj(Miller(|x|, Q', P))^((p^12 - 1) / r)`.

- `x = -0xd201000000010000` is the BLS parameter, which is negative.
- `P` is in `G1`, and `Q` is in `G2`.
- `Q'` is the untwisted image of `Q` on `E` over `Fp12`.

The Miller loop follows the optimal ate pairing of [the pairing-friendly curves draft][pfc], A.2.

The final exponentiation sends the result to the `r`-th roots of unity in `Fp12`.

The code is generic in the base field, as for `Fp2`.

[pfc]: https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-pairing-friendly-curves-11#appendix-A.2
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

variable {F : Type} [BaseField F]

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
def lineValue (c0 c2 c3 : Fp2 F) : Fp12 F :=
  ⟨⟨c0, c2, Fp2.zero⟩, ⟨Fp2.zero, c3, Fp2.zero⟩⟩

/-- Doubling step: `(T, f) ↦ (2T, f^2 l)`, with `l` the tangent at `T`, at `(xp, yp)`.

The line is the draft's line times `c w^3`, as above, with `c = -2 Y Z^3` for `T = (X, Y, Z)`. -/
def millerDouble (T : G2 F) (xp yp : F) (f : Fp12 F) : G2 F × Fp12 F :=
  let two := Fp2.ofFp (BaseField.ofNat 2)
  let three := Fp2.ofFp (BaseField.ofNat 3)
  let xx := T.x * T.x
  let zz := T.z * T.z
  -- The line function, case `Q_1 = Q_2`: `l := (3 * x_1^2) / (2 * y_1)`, on `E`.
  --
  -- On the twist, `x_1 = X / Z^2`, `y_1 = Y / Z^3`, and the slope is `lambda = 3 X^2 / (2 Y Z)`.
  --
  -- The line `lambda x_1 - y_1 - lambda xp w^2 + yp w^3`, times `2 Y Z^3` gives these coefficients.
  let c0 := three * xx * T.x - two * (T.y * T.y)
  let c2 := -(three * xx * zz * Fp2.ofFp xp)
  let c3 := two * T.y * zz * T.z * Fp2.ofFp yp
  -- A.2: `f := f^2 * l` and `T := T + T`, with `l` the line function of `T`, `T` at `P`.
  (T.double, f * f * lineValue c0 c2 c3)

/-- Addition step: `(T, f) ↦ (T + Q, f l)`, with `l` the line through `T` and `Q = (xq, yq)`.

The line is the draft's line times `c w^3`, as above, with `c = -D` for the `D` below.

The loop never adds `T = ±Q` on points of order `r`, so the draft's other cases never arise. -/
def millerAdd (T : G2 F) (xq yq : Fp2 F) (xp yp : F) (f : Fp12 F) : G2 F × Fp12 F :=
  let zz := T.z * T.z
  -- The line function, last case: `l := (y_2 - y_1) / (x_2 - x_1)`, on `E`.
  --
  -- On the twist, `x_1 = X / Z^2`, `y_1 = Y / Z^3`, and the slope is `lambda = N / D`.
  let n := yq * zz * T.z - T.y
  let d := (xq * zz - T.x) * T.z
  -- The line is written through `Q` rather than through `T`, so `Z` is not divided.
  --
  -- The line `lambda xq - yq - lambda xp w^2 + yp w^3`, times `D` gives these coefficients.
  let c0 := n * xq - d * yq
  let c2 := -(n * Fp2.ofFp xp)
  let c3 := d * Fp2.ofFp yp
  -- A.2: `f := f * l` and `T := T + Q`, with `l` the line function of `T`, `Q` at `P`.
  (G2.add T ⟨xq, yq, Fp2.one⟩, f * lineValue c0 c2 c3)

/-- Walk bits `n - 1` down to `0` of `s` from `(T, f)`.

At each bit it doubles `T`, then adds `Q` if the bit is set. -/
def millerSteps (s : Nat) (xq yq : Fp2 F) (xp yp : F) : Nat → G2 F → Fp12 F → Fp12 F
  | 0, _, f => f
  | n + 1, T, f =>
    -- A.2: the loop runs `i` from `L - 1` down to 0; here `i = n`.
    let (T, f) := millerDouble T xp yp f
    -- A.2: the addition step runs when `c_i = 1`, with `c_i` the bit `n` of `s`.
    let (T, f) := if (s >>> n) &&& 1 = 1 then millerAdd T xq yq xp yp f else (T, f)
    millerSteps s xq yq xp yp n T f

/-- The Miller loop of `s`, for the affine points `Q = (xq, yq)` of the twist and `P = (xp, yp)`.

The initial `T = Q` and `f = 1` consume the leading bit of `s`.

So the steps start one bit below it.

`Nat.log2 0 = 0`, so `s = 0` takes no steps. -/
def millerLoop (s : Nat) (q : Fp2 F × Fp2 F) (p : F × F) : Fp12 F :=
  -- A.2: `f := 1` and `T := Q`, then the loop from `L - 1`, with `L` the top bit index of `s`.
  millerSteps s q.1 q.2 p.1 p.2 s.log2 ⟨q.1, q.2, Fp2.one⟩ Fp12.one

/-! ## Final exponentiation -/

/-- The exponent `(p^12 − 1) / r`. -/
def finalExpExponent : Nat :=
  (Fp.modulus ^ 12 - 1) / Fr.modulus

/-- Raise `f` to `(p^12 − 1) / r`.

It follows [Hayashida, Hayasaka and Teruya][hht], §5, "BLS family with k = 12".

Their `x` is the BLS parameter, here `−|x|`.

For a nonzero input, the easy part outputs an element of the cyclotomic subgroup.

So the hard part squares with the cyclotomic formula, which also maps zero to zero.

The steps compute exactly `f^((p^12 − 1) / r)`, and a theorem proves it.

[hht]: https://eprint.iacr.org/2020/875
-/
def finalExponentiation (f : Fp12 F) : Fp12 F :=
  -- §5: `(p^12 - 1) / r = (p^6 - 1)(p^2 + 1) * Phi_12(p) / r`, with `Phi_12(p) = p^4 - p^2 + 1`.
  --
  -- The factor `p^6 - 1`: in this tower `f^(p^6)` is the conjugate of `f`, so one inversion.
  let t := f.conjugate * f.inverse
  -- The factor `p^2 + 1`: two Frobenius maps and one product.
  let m := t.frobenius.frobenius * t
  -- §5 (k = 12), by Theorem 4: `3 Phi_12(p) / r = (x - 1)^2 (x + p)(x^2 + p^2 - 1) + 3`.
  --
  -- With `x = -|x|`, the hard part is `h = ((|x| + 1)^2 / 3)(p - |x|)(|x|^2 + p^2 - 1) + 1`.
  --
  -- The element `m` satisfies `m^(p^6) = m^(-1)`, so its power by `-n` is the conjugate of `m^n`.
  --
  -- So `m^h` needs only powers by `|x|` and `(|x| + 1) / 3`, Frobenius maps and conjugates.
  --
  -- The exponents `|x|` and `(|x| + 1) / 3` have at most 64 bits.
  --
  -- `a = m^((x - 1)^2 / 3)`, which is `m^((|x| + 1)^2 / 3)`, since `3` divides `|x| + 1`.
  let a := (m.cyclotomicPow ((blsX + 1) / 3)).cyclotomicPow (blsX + 1)
  -- `b = a^(x + p)`, which is `a^p * conj(a^|x|)`.
  let b := a.frobenius * (a.cyclotomicPow blsX).conjugate
  -- `c = b^(x^2 + p^2 - 1)`, which is `(b^|x|)^|x| * b^(p^2) * conj(b)`.
  let c := (b.cyclotomicPow blsX).cyclotomicPow blsX * b.frobenius.frobenius * b.conjugate
  -- `m^h = c * m`, the `+ 1` of `h`.
  c * m

/-! ## The pairing -/

/-- The factor that one pair adds to the product of the pairing check.

It is the Miller loop of the pair, conjugated because the BLS parameter `x` is negative.

A pair with a point at infinity adds no factor, since its pairing is 1. -/
def pairFactor (pq : G1 F × G2 F) : Option (Fp12 F) :=
  if pq.1.isInfinity || pq.2.isInfinity then none
  -- For the negative `x`, A.2 starts with `T := -T` and subtracts `Q` on each digit `-1`.
  --
  -- Here the loop adds `Q` on the bits of `|x|`, and the conjugate stands for the inverse.
  --
  -- [Vercauteren](https://eprint.iacr.org/2008/096), §2.3: `f_{s,Q} = 1/(f_{-s,Q} v_{[s]Q})`.
  --
  -- The final exponentiation removes `v`, and maps the conjugate and the inverse to one value.
  else some (millerLoop blsX pq.2.toAffine pq.1.toAffine).conjugate

/-- The pairing `e(P, Q)`, an element of `Fp12`.

It is the final exponentiation of the factor of the pair.

A point at infinity gives 1. -/
def pairing (P : G1 F) (Q : G2 F) : Fp12 F :=
  match pairFactor (P, Q) with
  | none => Fp12.one
  -- A.2: `f := f^{(p^k - 1) / r}`.
  | some f => finalExponentiation f

/-- Returns `true` iff `∏ e(P_i, Q_i) = 1`.

The factors of the pairs are multiplied first, in the order of the pairs.

Then one final exponentiation applies to the whole product. -/
def pairingCheck (pairs : Array (G1 F × G2 F)) : Bool :=
  (finalExponentiation ((pairs.filterMap pairFactor).foldl (· * ·) Fp12.one)).isOne

end EthLib.Cryptography.Bls
