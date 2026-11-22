module

public import EthLib.Cryptography.BaseField
public import Mathlib.Algebra.Field.Defs

/-!
# Proofs: maps between base fields

A map between two base fields can respect every operation that an extension or a curve reads.

Then it commutes with each extension and curve built on them, one definition at a time.

So a fact that the kernel computes on one base field holds on the other.

A curve reads only the field operations, so a map that respects those is enough for it.

An injective such map into a field of Mathlib carries the laws of that field back to the operations.
-/

@[expose] public section

namespace EthLib.Cryptography

namespace FieldOps

/-- A map from `F` to `G` that respects every field operation. -/
structure Hom (F G : Type) [FieldOps F] [FieldOps G] where
  /-- The map of elements. -/
  toFun : F → G
  map_add : ∀ a b, toFun (a + b) = toFun a + toFun b
  map_sub : ∀ a b, toFun (a - b) = toFun a - toFun b
  map_mul : ∀ a b, toFun (a * b) = toFun a * toFun b
  map_neg : ∀ a, toFun (-a) = -toFun a
  map_zero : toFun zero = zero
  map_one : toFun one = one
  map_beq : ∀ a b, beq (toFun a) (toFun b) = beq a b
  map_isZero : ∀ a, isZero (toFun a) = isZero a
  map_inverse : ∀ a, toFun (inverse a) = inverse (toFun a)

instance {F G : Type} [FieldOps F] [FieldOps G] : CoeFun (Hom F G) (fun _ => F → G) :=
  ⟨Hom.toFun⟩

/-- An injective map of the field operations of `F` into a field of Mathlib, respecting each one. -/
structure Embedding (F K : Type) [FieldOps F] [Field K] where
  /-- The map of elements. -/
  toFun : F → K
  injective : Function.Injective toFun
  map_add : ∀ a b, toFun (a + b) = toFun a + toFun b
  map_sub : ∀ a b, toFun (a - b) = toFun a - toFun b
  map_mul : ∀ a b, toFun (a * b) = toFun a * toFun b
  map_neg : ∀ a, toFun (-a) = -toFun a
  map_zero : toFun FieldOps.zero = 0
  map_one : toFun FieldOps.one = 1
  map_inverse : ∀ a, toFun (FieldOps.inverse a) = (toFun a)⁻¹
  /-- The boolean equality holds exactly when the images are equal. -/
  beq_iff : ∀ a b, FieldOps.beq a b = true ↔ toFun a = toFun b
  /-- The zero test holds exactly when the image is zero. -/
  isZero_iff : ∀ a, FieldOps.isZero a = true ↔ toFun a = 0

end FieldOps

namespace BaseField

/-- A map from `F` to `G` that respects every operation of a base field. -/
structure Hom (F G : Type) [BaseField F] [BaseField G] extends FieldOps.Hom F G where
  map_ofNat : ∀ n, toFun (ofNat n) = ofNat n
  map_powNat : ∀ a n, toFun (powNat a n) = powNat (toFun a) n
  map_sqrt : ∀ a, sqrt (toFun a) = (sqrt a).map toFun
  map_sqrtCandidate : ∀ a, sqrtCandidate (toFun a) = toFun (sqrtCandidate a)
  map_sgn0 : ∀ a, sgn0 (toFun a) = sgn0 a

instance {F G : Type} [BaseField F] [BaseField G] : CoeFun (Hom F G) (fun _ => F → G) :=
  ⟨fun f => f.toFun⟩

end BaseField

end EthLib.Cryptography
