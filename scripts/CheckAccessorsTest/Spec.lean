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

The condition is copied into the instance that decides it, which is an implicit argument. -/
def cond (xs : Array Nat) : Nat := if xs[0]! ≠ 0 then 1 else 2

/-- `GetElem?.getElem!`, once.

The kernel's copy of the recursion, `sumFirsts._f`, holds the site.

The check reports it as `sumFirsts`.

The equation lemmas that Lean generates for the recursion repeat the site, and are skipped. -/
def sumFirsts : List (Array Nat) → Nat
  | [] => 0
  | xs :: rest => xs[0]! + sumFirsts rest

/-- A theorem is searched in its statement: `GetElem?.getElem!`, once.

Its proof computes nothing, so it is not searched. -/
theorem first_eq (xs : Array Nat) : first xs = xs[0]! := rfl

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
