module

public import Lean

set_option doc.verso true

/-!
# Source inspection with local syntax

Attribute inspection must not parse bodies with notation that disappears after import.

Literal text and syntax quotations do not apply attributes.
-/

@[expose] public section

namespace CheckTheoremsTest.LocalSyntax

local infix:65 " ⋆⋆ " => Nat.add

/-- The local operator is absent from the imported parser environment. -/
def localValue (n : Nat) : Nat := n ⋆⋆ 0

-- Leave this theorem without a docstring so documentation examples can copy one without warning.
@[simp] theorem localValue_eq (n : Nat) : localValue n = n := Nat.add_zero n

/-- Attribute-looking text inside a string does not register a rule. -/
def text : String := "attribute [not_an_attribute] unknown"

/-- Raw strings are literals too. -/
def rawText : String := r#"attribute [not_an_attribute] unknown"#

/-- Name literals are not attribute commands. -/
def name : Lean.Name := `attribute

/-- Escaped identifiers do not introduce commands. -/
def «attribute» : Nat := 0

/- A nested comment must remain a comment: /- attribute [not_an_attribute] unknown -/ -/

/-- A command quotation constructs syntax instead of applying its attribute. -/
def quoted : Lean.MacroM (Lean.TSyntax `command) :=
  `(command| attribute [inherit_doc Nat.add_zero] Nat.add_zero)

/-- A name literal and a later theorem reference are ordinary function arguments. -/
def consume (_name : Lean.Name) (_attrs : List Lean.Name)
    (_target : ∀ n : Nat, n + 0 = n) : Nat := 0

#check consume `attribute [name] Nat.add_zero

namespace Dot

/-- A dotted identifier ending in the keyword is also an ordinary function. -/
def «attribute» (_attrs : List Lean.Name) (_target : ∀ n : Nat, n + 0 = n) : Nat := 0

end Dot

#check Dot.attribute [name] Nat.add_zero

/-!
```lean
attribute [inherit_doc Nat.add_zero] CheckTheoremsTest.LocalSyntax.localValue_eq
```
-/

/--
```lean
attribute [inherit_doc Nat.add_zero] CheckTheoremsTest.LocalSyntax.localValue_eq
```
-/
def documented : Nat := 0

end CheckTheoremsTest.LocalSyntax
