module

/-!
# `CheckDeclsForeign`

Declarations from outside the checked scope, as a dependency would provide them.
The fixtures in `CheckDeclsTest` use them, and the check must still see what they bring in.
-/

@[expose] public section

namespace CheckDeclsForeign

/-- An axiom of a dependency. -/
axiom T : Type

/-- A second axiom of a dependency, used only through `Cycle`. -/
axiom U : Type

/-- A proposition of a dependency that holds only if its axiom has an element. -/
def P : Prop := Nonempty U

/-- An inductive type of a dependency whose constructor carries its axiom, through `P`.

The type inherits the axiom from its constructor, which takes a proof of `P`. -/
inductive Cycle where
  | mk (h : P)

mutual

/-- An inductive type of a dependency, declared with `Right`, whose own constructor is plain. -/
inductive Left where
  | a

/-- The other type of the declaration, whose constructor carries the axiom through `P`. -/
inductive Right where
  | b (h : P)

end

/-- An opaque constant of a dependency. -/
opaque hiddenNat : Nat

end CheckDeclsForeign
