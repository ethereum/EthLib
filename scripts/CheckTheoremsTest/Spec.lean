module

/-!
# Theorems retained by definitions, instances and simplification

Findings have no definition or instance consumer and no `simp` attribute.
-/

@[expose] public section

namespace CheckTheoremsTest.Spec

/-- A definition uses this theorem directly. -/
theorem direct_bound (n : Nat) : n < n + 1 := Nat.lt_succ_self n

/-- A proof in a definition's result retains its theorem. -/
def direct (n : Nat) : Fin (n + 1) := ⟨n, direct_bound n⟩

/-- A public computational helper retains this theorem. -/
theorem nested_bound (n : Nat) : n < n + 1 := Nat.lt_succ_self n

/-- The helper's enclosing function need not call it. -/
def with_unused_helper (n : Nat) : Nat := n
where
  /-- A computational definition remains a root under its parent's namespace. -/
  helper (n : Nat) : Fin (n + 1) := ⟨n, nested_bound n⟩

/-- A retained theorem uses this helper. -/
theorem transitive_helper (n : Nat) : n < n + 1 := Nat.lt_succ_self n

/-- A definition uses this theorem, which retains its own helper. -/
theorem transitive_bound (n : Nat) : n < n + 1 := transitive_helper n

/-- The check follows the complete chain from this definition. -/
def transitive (n : Nat) : Fin (n + 1) := ⟨n, transitive_bound n⟩

/-- The theorem belongs only to another unneeded theorem's proof. -/
theorem unused_helper (n : Nat) : n + 0 = n := Nat.add_zero n

/-- Both this theorem and its helper are findings. -/
theorem unused (n : Nat) : n + 0 = n := unused_helper n

/-- Only a definition in a property module uses this theorem. -/
theorem used_only_from_proofs (n : Nat) : n < n + 1 := Nat.lt_succ_self n

/-- Only a definition in an export module uses this theorem. -/
theorem used_only_from_exports (n : Nat) : n < n + 1 := Nat.lt_succ_self n

/-- Only a simplification theorem uses this private helper. -/
private theorem simp_helper (n : Nat) : n + 0 = n := Nat.add_zero n

/-- A definition whose simplification rule is public. -/
def simpValue (n : Nat) : Nat := n + 0

/-- The simplification attribute exempts this theorem from findings. -/
@[simp] theorem simpValue_eq (n : Nat) : simpValue n = n := simp_helper n

/-- Only the reverse simplification rule uses this private helper. -/
private theorem reverse_helper (n : Nat) : n = n + 0 := (Nat.add_zero n).symm

/-- A definition with a reverse simplification rule. -/
def reverseValue (n : Nat) : Nat := n + 0

/-- The persistent reverse attribute exempts this theorem from findings. -/
theorem reverse_eq (n : Nat) : n = reverseValue n := reverse_helper n

attribute [simp ←] reverse_eq

/-- Only the imported simplification rule uses this helper. -/
theorem removed_helper (n : Nat) : n + 0 = n := Nat.add_zero n

/-- A definition whose rule is erased in this module. -/
def removedValue (n : Nat) : Nat := n + 0

/-- The erasure below is local to this module, so importers still receive this rule. -/
@[simp] theorem removed_eq (n : Nat) : removedValue n = n := removed_helper n

attribute [-simp] removed_eq

/-- A local simplification attribute does not retain this theorem after its section ends. -/
theorem local_eq (n : Nat) : removedValue n = n := Nat.add_zero n

section

attribute [local simp] local_eq

end

/-- A proposition-valued instance retains this proof dependency. -/
theorem instance_bound (n : Nat) : n < n + 1 := Nat.lt_succ_self n

/-- A proposition-valued class supplies an instance root. -/
class HasBound (n : Nat) : Prop where
  /-- The supplied bound. -/
  bound : n < n + 1

/-- An instance is retained even when no other definition uses it. -/
instance (n : Nat) : HasBound n := ⟨instance_bound n⟩

/-- A definition local to an unneeded proof must not retain this theorem. -/
theorem proof_local_helper : True := True.intro

/-- The helper definition belongs to this unneeded proof, so neither roots the other. -/
theorem with_local_definition : True := helper.property
where
  /-- A generated definition of a theorem is not a specification entry point. -/
  helper : { _value : Nat // True } := ⟨0, proof_local_helper⟩

/-- Structural recursion produces equation lemmas which are not independent findings. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + n + 1

/-- Unfolding the recursion requests its generated equation lemmas. -/
theorem sumTo_succ (n : Nat) : sumTo (n + 1) = sumTo n + n + 1 := by
  simp only [sumTo]

/-- A user theorem with a generated-looking name is still a finding. -/
theorem orphan.eq_1 (n : Nat) : n + 0 = n := Nat.add_zero n

/-- A second generated-looking suffix must not hide a user theorem. -/
theorem orphan._proof_1 (n : Nat) : n + 0 = n := Nat.add_zero n

/-- A generated-looking suffix under a real definition still names a user theorem. -/
theorem direct._proof_99 (n : Nat) : n + 0 = n := Nat.add_zero n

/-- This private finding shares its user-facing name with one in another module. -/
private theorem private_unused (n : Nat) : n + 0 = n := Nat.add_zero n

/-- Only the unneeded private theorem's local definition uses this dependency. -/
theorem private_local_helper : True := True.intro

/-- A private theorem with a local definition is a finding too. -/
private theorem private_with_local_definition : True := helper.property
where
  /-- This definition belongs to its private theorem, under the original private prefix. -/
  helper : { _value : Nat // True } := ⟨0, private_local_helper⟩

end CheckTheoremsTest.Spec

namespace UnrelatedNamespace

/-- The defining module determines scope even when the namespace differs from the library. -/
theorem unused (n : Nat) : n + 0 = n := Nat.add_zero n

end UnrelatedNamespace
