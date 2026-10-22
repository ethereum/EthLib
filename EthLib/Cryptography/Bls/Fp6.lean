import EthLib.Cryptography.Bls.Fp2

/-!
# `Fp6`

The cubic extension `Fp6 = Fp2[v] / (v³ − ξ)` where `ξ = 1 + i ∈ Fp2`.
Elements are written `c0 + c1·v + c2·v²` with each coefficient in `Fp2`.

Multiplication uses the school-book formula plus the reduction
`v³ = ξ`. Concretely, expanding `(a0 + a1·v + a2·v²)(b0 + b1·v + b2·v²)`
and collecting:

  c0 = a0·b0 + ξ·(a1·b2 + a2·b1)
  c1 = a0·b1 + a1·b0 + ξ·(a2·b2)
  c2 = a0·b2 + a1·b1 + a2·b0

Inversion uses the formula derived from the norm in `Fp6` over `Fp2`.
-/

namespace EthLib.Cryptography.Bls

/-- An element of `Fp6`, written `c0 + c1·v + c2·v²` with `v³ = 1 + i`. -/
structure Fp6 where
  c0 : Fp2
  c1 : Fp2
  c2 : Fp2
deriving Inhabited, BEq, Repr

namespace Fp6

@[inline] def zero : Fp6 := ⟨Fp2.zero, Fp2.zero, Fp2.zero⟩
@[inline] def one  : Fp6 := ⟨Fp2.one,  Fp2.zero, Fp2.zero⟩
@[inline] def v    : Fp6 := ⟨Fp2.zero, Fp2.one,  Fp2.zero⟩

@[inline] def ofFp2 (x : Fp2) : Fp6 := ⟨x, Fp2.zero, Fp2.zero⟩

@[inline] def add (a b : Fp6) : Fp6 := ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2⟩
@[inline] def sub (a b : Fp6) : Fp6 := ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2⟩
@[inline] def neg (a : Fp6)   : Fp6 := ⟨-a.c0, -a.c1, -a.c2⟩

/-- School-book multiplication with `v³ = 1 + i`. -/
def mul (a b : Fp6) : Fp6 :=
  let t0 := a.c0 * b.c0
  let t1 := a.c1 * b.c1
  let t2 := a.c2 * b.c2
  -- (a1+a2)(b1+b2) − a1·b1 − a2·b2 = a1·b2 + a2·b1
  let c0 := ((a.c1 + a.c2) * (b.c1 + b.c2) - t1 - t2).mulByOnePlusI + t0
  let c1 := (a.c0 + a.c1) * (b.c0 + b.c1) - t0 - t1 + t2.mulByOnePlusI
  let c2 := (a.c0 + a.c2) * (b.c0 + b.c2) - t0 - t2 + t1
  ⟨c0, c1, c2⟩

instance : Add Fp6 := ⟨add⟩
instance : Sub Fp6 := ⟨sub⟩
instance : Mul Fp6 := ⟨mul⟩
instance : Neg Fp6 := ⟨neg⟩

@[inline] def beq (a b : Fp6) : Bool :=
  a.c0.beq b.c0 && a.c1.beq b.c1 && a.c2.beq b.c2
@[inline] def isZero (a : Fp6) : Bool :=
  a.c0.isZero && a.c1.isZero && a.c2.isZero

/-- Multiplication by `v` (cyclic shift + ξ-twist). -/
@[inline] def mulByV (a : Fp6) : Fp6 :=
  -- (c0 + c1·v + c2·v²) · v = c0·v + c1·v² + c2·v³
  --                          = ξ·c2 + c0·v + c1·v²
  ⟨a.c2.mulByOnePlusI, a.c0, a.c1⟩

/-- Multiplicative inverse via the norm formula. Caller must ensure
`a ≠ 0`. -/
def inverse (a : Fp6) : Fp6 :=
  let xi := Fp2.mulByOnePlusI
  let t0 := a.c0 * a.c0 - xi (a.c1 * a.c2)
  let t1 := xi (a.c2 * a.c2) - a.c0 * a.c1
  let t2 := a.c1 * a.c1 - a.c0 * a.c2
  let det := a.c0 * t0 + xi (a.c2 * t1) + xi (a.c1 * t2)
  let invDet := det.inverse
  ⟨t0 * invDet, t1 * invDet, t2 * invDet⟩

instance : Div Fp6 := ⟨fun a b => a * b.inverse⟩

end Fp6

end EthLib.Cryptography.Bls
