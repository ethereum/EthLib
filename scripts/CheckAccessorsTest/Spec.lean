module

/-!
# Sites that the accessor check counts, and constructs that it must skip

Each definition names, in its doc comment, the entry that the check reports for it.
-/

@[expose] public section

namespace CheckAccessorsTest.Spec

/-- `GetElem?.getElem!`, once. -/
def first (xs : Array Nat) : Nat := xs[0]!

/-- `ByteArray.get!` and `ByteArray.set!`, once each. -/
def bump (b : ByteArray) : ByteArray := b.set! 0 (b.get! 0 + 1)

/-- `Array.back!`, once. -/
def last (xs : Array Nat) : Nat := xs.back!

/-- `panic!` elaborates to `panicWithPosWithDecl`, once. -/
def nonzero (n : Nat) : Nat := if n = 0 then panic! "zero" else n

/-- Two sites of one accessor in one declaration: `GetElem?.getElem!`, twice. -/
def twice (xs : Array Nat) : Nat := xs[0]! + xs[1]!

/-- `GetElem?.getElem!`, once.

The condition is copied into the instance that decides it, an argument the check does not search. -/
def cond (xs : Array Nat) : Nat := if xs[0]! ≠ 0 then 1 else 2

/-- `GetElem?.getElem!`, once.

The kernel's copy of the recursion holds the site.

The check reports it under the name of this definition. -/
def sumFirsts : List (Array Nat) → Nat
  | [] => 0
  | xs :: rest => xs[0]! + sumFirsts rest

/-- The proof makes Lean generate the equation lemmas of the recursion above.

They repeat its site, and the check skips them, so this theorem adds no entry. -/
theorem sumFirsts_cons (xs : Array Nat) (rest : List (Array Nat)) :
    sumFirsts (xs :: rest) = sumFirsts [xs] + sumFirsts rest := by
  simp [sumFirsts]

/-- A theorem is searched in its statement: `GetElem?.getElem!`, once.

Its proof computes nothing, so it is not searched. -/
theorem first_eq (xs : Array Nat) : first xs = xs[0]! := rfl

/-- A site in a hypothesis of a statement: `GetElem?.getElem!`, once. -/
theorem first_of_zero (xs : Array Nat) (h : xs[0]! = 0) : first xs = 0 := h

/-- A site in a proof only is not searched, so this theorem has no entry. -/
theorem inProof (xs : Array Nat) : True := (fun _ => trivial) xs[0]!

/-- A site in a local definition: `GetElem?.getElem!`, once. -/
def withLet (xs : Array Nat) : Nat :=
  let a := xs[0]!
  a + a

/-- `ByteArray.get!`, once.

The site is in the type, and Lean copies it into the value as an explicit argument.

The check counts the larger of the two counts, not their sum. -/
def isOne (b : ByteArray) : Decidable (b.get! 0 = 1) := decEq _ _

/-- A wrapper whose name has no `!`: `GetElem?.getElem!`, once, here. -/
def at0 (xs : Array Nat) : Nat := xs[0]!

/-- The callers of a wrapper are not counted, so this declaration has no entry. -/
def useAt0 (xs : Array Nat) : Nat := at0 xs + at0 xs

/-- An explicit default is no site, so this declaration has no entry. -/
def safe (xs : Array Nat) : Nat := xs.getD 0 0

/-- A string that spells `xs[0]!` is no site, so this declaration has no entry. -/
def spelled : String := "xs[0]!"

/-- A private definition is found, and reported under its name without the private prefix. -/
private def hidden (xs : Array Nat) : Nat := xs[0]!

end CheckAccessorsTest.Spec
