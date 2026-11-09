module


/-!
# Base fields of extension towers

The operations that an extension field, a curve or a pairing reads from its base field.

The extensions and curves are written once, generic in the base field.

The executable code instantiates them at the field type of the specification.

Proofs can instantiate them at Mathlib's `ZMod p`, so that the kernel computes on integers mod `p`.

A map between two base fields that respects these operations then carries one result to the other.
-/

@[expose] public section

namespace EthLib.Cryptography

/-- The operations of a base field, with the notation of the sum, difference, product and negation.

The class states no laws: proofs take the laws from the field structure of an instance. -/
class BaseField (F : Type) extends Add F, Sub F, Mul F, Neg F where
  /-- The additive identity. -/
  zero : F
  /-- The multiplicative identity. -/
  one : F
  /-- The image of a natural number `n`, the sum of `n` ones. -/
  ofNat : Nat → F
  /-- Equality as a boolean. -/
  beq : F → F → Bool
  /-- Whether the element is zero. -/
  isZero : F → Bool
  /-- The multiplicative inverse.

  Each instance states its value at zero. -/
  inverse : F → F
  /-- The power by a natural number. -/
  powNat : F → Nat → F
  /-- A square root, or `none` when the element is not a square.

  Each instance states which of the two roots it returns. -/
  sqrt : F → Option F
  /-- A candidate square root: its square is the input or the negation of the input.

  For a field of order `q = 3 mod 4`, the power `a^((q + 1) / 4)` has this property.

  The class states no law.

  Without this property, the square root in the quadratic extension can return a non-root. -/
  sqrtCandidate : F → F
  /-- The sign `sgn0` of RFC 9380, §4.1: whether the canonical integer of the element is odd. -/
  sgn0 : F → Bool

end EthLib.Cryptography
