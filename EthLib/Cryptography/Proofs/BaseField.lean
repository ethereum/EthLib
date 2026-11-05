module

public import EthLib.Cryptography.BaseField

/-!
# Proofs: maps between base fields

A map between two base fields can respect every operation that an extension or a curve reads.

Then it commutes with each extension and curve built on them, one definition at a time.

So a fact that the kernel computes on one base field holds on the other.
-/

@[expose] public section

namespace EthLib.Cryptography.BaseField

/-- A map from `F` to `G` that respects every operation of a base field. -/
structure Hom (F G : Type) [BaseField F] [BaseField G] where
  /-- The map of elements. -/
  toFun : F → G
  map_add : ∀ a b, toFun (a + b) = toFun a + toFun b
  map_sub : ∀ a b, toFun (a - b) = toFun a - toFun b
  map_mul : ∀ a b, toFun (a * b) = toFun a * toFun b
  map_neg : ∀ a, toFun (-a) = -toFun a
  map_zero : toFun zero = zero
  map_one : toFun one = one
  map_ofNat : ∀ n, toFun (ofNat n) = ofNat n
  map_beq : ∀ a b, beq (toFun a) (toFun b) = beq a b
  map_isZero : ∀ a, isZero (toFun a) = isZero a
  map_inverse : ∀ a, toFun (inverse a) = inverse (toFun a)
  map_powNat : ∀ a n, toFun (powNat a n) = powNat (toFun a) n
  map_sqrt : ∀ a, sqrt (toFun a) = (sqrt a).map toFun
  map_sgn0 : ∀ a, sgn0 (toFun a) = sgn0 a

instance {F G : Type} [BaseField F] [BaseField G] : CoeFun (Hom F G) (fun _ => F → G) :=
  ⟨Hom.toFun⟩

end EthLib.Cryptography.BaseField
