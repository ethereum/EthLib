module

/-!
# `BinaryField.GF64`

The field `K = GF(2^64)`, as the quotient `GF(2)[x]/(f)` with `f = x^64 + x^4 + x^3 + x + 1`.

Lidl and Niederreiter, Finite Fields, chapter 2, give this representation of `GF(2^n)`.

An element is a polynomial in `x` of degree below 64 with coefficients in `{0, 1}`.

It is stored as one 64-bit word, and bit `i` of the word is the coefficient of `x^i`.

So the word `0x2` is `x`, and the word `0x3` is `x + 1`.

Addition is the exclusive or of the words.

Multiplication is the carry-less product of the words, reduced modulo `f`.

The inverse is the power `a^(2^64 - 2)`, by the chain of Itoh and Tsujii.

So zero has the inverse zero.

It is not intended to be constant-time.
-/

@[expose] public section

namespace EthLib.Cryptography.BinaryField

/-- An element of K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1).

Bit `i` of `bits` is the coefficient of `x^i`. -/
structure GF64 where
  bits : UInt64
  deriving DecidableEq, Repr, Inhabited

namespace GF64

/-- The low 64 bits of `x^64` modulo the field polynomial: `x^4 + x^3 + x + 1`. -/
def MODULUS_LOW : UInt64 := 0x1b

/-- The zero polynomial. -/
def zero : GF64 := ⟨0⟩

/-- The constant polynomial `1`. -/
def one : GF64 := ⟨1⟩

/-- The generator `g = x`. -/
def g : GF64 := ⟨2⟩

/-- Addition: the exclusive or of the coefficient words. -/
def add (a b : GF64) : GF64 := ⟨a.bits ^^^ b.bits⟩

/-- The carry-less product of two words, as (high word, low word).

Bit `k` of the 128-bit result is the parity of the pairs `(i, j)` with `i + j = k`.

Only the pairs where bit `i` of `a` and bit `j` of `b` are both set count.

Each set bit `i` of `b` adds `a` shifted up by `i` places.

The low word takes `a <<< i`, and the high word takes the top `i` bits of `a`. -/
def clmul (a b : UInt64) : UInt64 × UInt64 :=
  (List.range 64).foldl (fun (hi, lo) i =>
    if (b >>> i.toUInt64) &&& 1 = 1 then
      (if i = 0 then hi else hi ^^^ (a >>> (64 - i).toUInt64),
        lo ^^^ (a <<< i.toUInt64))
    else (hi, lo)) (0, 0)

/-- Reduce a carry-less product `hi * x^64 + lo` modulo `x^64 + x^4 + x^3 + x + 1`.

Modulo the field polynomial, `hi * x^64` equals `hi * (x^4 + x^3 + x + 1)`.

That product is `hi`, `hi <<< 1`, `hi <<< 3` and `hi <<< 4` added together.

Its bits past `x^63` are the words `hi >>> 63`, `hi >>> 61` and `hi >>> 60`.

Their sum has degree below 4, so it folds once more, now with no bit past `x^63`.

So the result adds `v = hi + spill` times `x^4 + x^3 + x + 1` to `lo`, where `spill` is that sum. -/
def reduce (hi lo : UInt64) : UInt64 :=
  let v := hi ^^^ ((hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60))
  lo ^^^ v ^^^ (v <<< 1) ^^^ (v <<< 3) ^^^ (v <<< 4)

/-- Multiplication: the carry-less product of the words, reduced modulo the field polynomial. -/
def mul (a b : GF64) : GF64 := let (hi, lo) := clmul a.bits b.bits; ⟨reduce hi lo⟩

/-- The square `a * a`. -/
def square (a : GF64) : GF64 := mul a a

/-- `a^(2^n)`: `n` squarings. -/
def squareN : Nat → GF64 → GF64
  | 0, a => a
  | n + 1, a => squareN n (square a)

/-- `a^n` by square and multiply, low bit first.

The power is `1` at `n = 0`.

Otherwise it is `(a^2)^(n / 2)`, times `a` when `n` is odd. -/
def pow (a : GF64) (n : Nat) : GF64 :=
  if n = 0 then one
  else
    let rest := pow (square a) (n / 2)
    if n % 2 = 1 then mul a rest else rest
termination_by n
decreasing_by omega

/-- The inverse `a^(2^64 - 2)`, by the chain of Itoh and Tsujii.

Each `tk` is `a^(2^k - 1)`, and `t(j + k)` is `tj` raised to `2^k`, times `tk`.

The last step squares `t63`, so the exponent is `2 * (2^63 - 1) = 2^64 - 2`.

The inverse of zero is zero. -/
def inv (a : GF64) : GF64 :=
  let t1 := a
  let t2 := mul (squareN 1 t1) t1
  let t3 := mul (squareN 1 t2) t1
  let t6 := mul (squareN 3 t3) t3
  let t12 := mul (squareN 6 t6) t6
  let t24 := mul (squareN 12 t12) t12
  let t48 := mul (squareN 24 t24) t24
  let t60 := mul (squareN 12 t48) t12
  let t63 := mul (squareN 3 t60) t3
  squareN 1 t63

instance : Zero GF64 := ⟨zero⟩

instance : One GF64 := ⟨one⟩

instance : Add GF64 := ⟨add⟩

instance : Mul GF64 := ⟨mul⟩

instance : Inv GF64 := ⟨inv⟩

instance : Pow GF64 Nat := ⟨pow⟩

/-- Hash an element by its coefficient word, for hash maps keyed by addresses. -/
instance : Hashable GF64 := ⟨fun a => hash a.bits⟩

end GF64

end EthLib.Cryptography.BinaryField
