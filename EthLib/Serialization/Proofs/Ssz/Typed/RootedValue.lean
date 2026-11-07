module

public import EthLib.Serialization.Ssz.Typed.RootedValue
public import EthLib.Serialization.Proofs.Ssz.Typed.Class

/-!
# Proofs: rooted values are lawful

A rooted value is built with the root of its value, so its kept root is the root of the value.

The other laws are those of the value's type.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open SszType

variable {α : Type} [SszType α] [LawfulSszType α]

/-- The kept root of a rooted value is the root of its untyped value. -/
theorem Rooted.root_eq (r : Rooted α) :
    root r = Ssz.hashTreeRoot (desc (Rooted α)) (toValue r) := by
  change r.cached.get = _
  rw [r.built, LawfulSszType.root_eq]
  rfl

/-- A rooted value is lawful when its value is. -/
instance : LawfulSszType (Rooted α) where
  wellFormed := LawfulSszType.wellFormed (α := α)
  fits r := LawfulSszType.fits r.value
  ofValue_toValue r := by
    change Rooted.of <$> (ofValue (toValue r.value) : Except Err α) = .ok r
    rw [LawfulSszType.ofValue_toValue]
    exact congrArg Except.ok (Rooted.ext rfl)
  toValue_of_ofValue {value r} made := by
    change Rooted.of <$> (ofValue value : Except Err α) = .ok r at made
    cases read : (ofValue value : Except Err α) with
    | error fault => simp [read, Functor.map, Except.map] at made
    | ok w =>
      simp only [read, Functor.map, Except.map, Except.ok.injEq] at made
      subst made
      exact LawfulSszType.toValue_of_ofValue (α := α) read
  root_eq := Rooted.root_eq

end EthLib.Serialization.Ssz
