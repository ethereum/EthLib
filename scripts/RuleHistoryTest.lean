module

/-!
# Rules that the rule history must list, and declarations that it must skip

A fork type of three forks stands in for the forks of Ethereum, so each rule gives three lines.

Each definition says, in its doc comment, the lines that the tool writes for it.

`scripts/test_rule_history.sh` builds this library and compares the lines.
-/

@[expose] public section

namespace RuleHistoryTest.Base

/-- Three forks, in order. -/
inductive Fork where
  | early
  | middle
  | late
  deriving DecidableEq

/-- The position of a fork. -/
def Fork.toNat : Fork → Nat
  | .early => 0
  | .middle => 1
  | .late => 2

instance : LE Fork := ⟨fun a b => a.toNat ≤ b.toNat⟩

instance (a b : Fork) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

/-- A value that exists from the fork `f` on. -/
def Since (f fork : Fork) (α : Type) : Type := f ≤ fork → α

end RuleHistoryTest.Base

namespace RuleHistoryTest.Rules

open RuleHistoryTest.Base

/-- A constant: one line, with `-` for the fork. -/
def limit : Nat := 24576

/-- One line per fork: 50, 200 and 200. -/
def cost : Fork → Nat
  | .early => 50
  | _ => 200

/-- Two lines per fork, one for each `Bool`: 800, 2100 and 2100 cold, and 100 warm. -/
def access (fork : Fork) (warm : Bool) : Nat :=
  if warm then 100 else if fork = .early then 800 else 2100

/-- One line per fork, `none` where the rule has no value: none, none and `some 6`. -/
def target : Fork → Option Nat
  | .late => some 6
  | _ => none

/-- Two fields of type `Nat`, one of type `UInt64`, and one of another type, which is skipped. -/
structure Schedule where
  base : Nat
  refund : Nat
  cap : UInt64
  enabled : Bool

/-- One line per fork for each field of type `Nat` or `UInt64`.

Base is 21000, refund is 15000, 4800 and 4800, and cap is 6, 9 and 9. -/
def schedule : Fork → Schedule
  | .early => ⟨21000, 15000, 6, false⟩
  | _ => ⟨21000, 4800, 9, true⟩

/-- From `middle` on: base none, 6 and 9, refund none, 0 and 1, and cap none, 8 and 12. -/
def blobs : (fork : Fork) → Since .middle fork Schedule
  | .late, _ => ⟨9, 1, 12, true⟩
  | _, _ => ⟨6, 0, 8, true⟩

/-- Another argument than the fork: skipped. -/
def preset (scale : Nat) (fork : Fork) : Nat := scale * cost fork

/-- A value of another type than `Nat`: skipped. -/
def label : Fork → String
  | .early => "early"
  | _ => "later"

/-- An instance: skipped. -/
instance : Inhabited Schedule := ⟨schedule .early⟩

/-- A theorem: skipped. -/
theorem cost_late : cost .late = 200 := rfl

end RuleHistoryTest.Rules

namespace RuleHistoryTest.Other

/-- A constant outside the scope that the test passes: skipped. -/
def stray : Nat := 1

end RuleHistoryTest.Other
