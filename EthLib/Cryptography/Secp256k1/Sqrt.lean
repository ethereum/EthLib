module

public import EthLib.Cryptography.Secp256k1.Montgomery

/-!
# `Secp256k1.Sqrt`

The square root in the base field, by Euler's criterion.

Since `p = 3 mod 4`, a square `a` has the root `c = a^((p + 1) / 4)`.

The power runs in Montgomery form, by a fixed chain of squarings and products.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

namespace Montgomery

/-- Apply a step `n` times, with the four words of each value as separate arguments.

The words stay in registers between steps, so no value is allocated on the way. -/
@[noinline, specialize step] def repeatWords (step : Montgomery → Montgomery) :
    Nat → (w0 w1 w2 w3 : UInt64) → (Raw.mk w0 w1 w2 w3).val < Fp.modulus → Montgomery
  | 0, w0, w1, w2, w3, h => ⟨⟨w0, w1, w2, w3⟩, h⟩
  | n + 1, w0, w1, w2, w3, h =>
    let a := step ⟨⟨w0, w1, w2, w3⟩, h⟩
    repeatWords step n a.raw.w0 a.raw.w1 a.raw.w2 a.raw.w3 a.lt

/-- `a^(2^n)`, by `n` squarings. -/
@[inline] def squareTimes (n : Nat) (a : Montgomery) : Montgomery :=
  repeatWords square n a.raw.w0 a.raw.w1 a.raw.w2 a.raw.w3 a.lt

/-- `a^((p + 1) / 4)`, by the runs of ones in the binary form of the exponent.

In binary, the exponent is 223 ones, a zero, 22 ones, four zeros, two ones and two zeros.

Up to `x223`, each `x_k` is `a^(2^k - 1)`: `x_j` squared `k` times, times `x_k`, is `x_(j + k)`.

The last three steps append the remaining bits of the exponent, in the same way.

The chain is the one of libsecp256k1, in `field_impl.h` at v0.6.0:
<https://github.com/bitcoin-core/secp256k1/blob/v0.6.0/src/field_impl.h#L49-L122> -/
@[inline] def sqrtCandidate (a : Montgomery) : Montgomery :=
  let x2 := squareTimes 1 a * a
  let x3 := squareTimes 1 x2 * a
  let x6 := squareTimes 3 x3 * x3
  let x9 := squareTimes 3 x6 * x3
  let x11 := squareTimes 2 x9 * x2
  let x22 := squareTimes 11 x11 * x11
  let x44 := squareTimes 22 x22 * x22
  let x88 := squareTimes 44 x44 * x44
  let x176 := squareTimes 88 x88 * x88
  let x220 := squareTimes 44 x176 * x44
  let x223 := squareTimes 3 x220 * x3
  let x246 := squareTimes 23 x223 * x22
  let x252 := squareTimes 6 x246 * x2
  squareTimes 2 x252

/-- A square root of `a`, or `none` when `a` is not a square. -/
@[inline] def sqrt (a : Montgomery) : Option Montgomery :=
  let c := sqrtCandidate a
  if square c = a then some c else none

end Montgomery

/-- A square root of `a`, or `none` when `a` is not a square.

Since `p = 3 mod 4`, a square `a` has the root `c = a^((p + 1) / 4)`.

By Euler's criterion, `c^2 = a^((p + 1) / 2) = a * a^((p - 1) / 2) = a`.

When `a` is not a square, `c^2 != a`, so the check rejects it.

The power and the check run in Montgomery form. -/
def Fp.sqrt (a : Fp) : Option Fp :=
  (Montgomery.sqrt (Montgomery.ofFin a)).map Montgomery.toFin

end EthLib.Cryptography.Secp256k1
