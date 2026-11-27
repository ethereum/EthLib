module

public import EthLib.Base.Fork

/-!
# Rules of the fixtures, each with a window
-/

@[expose] public section

namespace ProofCoverageTest

open EthLib.Base

/-- No fork binder, so every beacon fork. -/
def eligible (n : Nat) : Bool := n == 0

/-- From Altair on. -/
def sync (fork : Fork) (_altair : .altair ≤ fork) (n : Nat) : Nat := n

/-- From Glamsterdam on. -/
def payload (fork : Fork) (_gloas : .glamsterdam ≤ fork) : Nat := 0

/-- Phase 0 only. -/
def early (fork : Fork) (_before : fork < .altair) : Nat := 0

/-- The two forks that its type names, Fusaka and Glamsterdam. -/
def upgrade (x : Since .fusaka .fusaka Nat) : Since .glamsterdam .glamsterdam Nat :=
  fun _ => x (Nat.le_refl _)

/-- Another hypothesis on the fork, so no window can be read. -/
def odd (fork : Fork) (_h : fork ≠ .altair) : Nat := 0

/-- A structure, whose projection is no rule. -/
structure Pair where
  left : Nat
  right : Nat

/-- An instance is no rule. -/
instance : Inhabited Pair := ⟨⟨0, 0⟩⟩

/-- A private definition is no rule. -/
private def hidden : Nat := 0

/-- A theorem of a specification module touches nothing. -/
theorem eligible_zero : eligible 0 = true := rfl

end ProofCoverageTest
