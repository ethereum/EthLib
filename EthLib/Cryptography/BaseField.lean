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
  /-- Equality as a boolean. -/
  beq : F → F → Bool
  /-- Whether the element is zero. -/
  isZero : F → Bool
  /-- The multiplicative inverse.

  Each instance states its value at zero. -/
  inverse : F → F

end EthLib.Cryptography
