import CheckTheoremsAttributesTest.Attributes

/-!
# Compiler, tactic and custom theorem attributes

The checker must stop before recommending that an attributed theorem move to a property module.
-/

namespace CheckTheoremsAttributesTest

/-- Two equal functions give a valid compiler replacement theorem. -/
def slow (n : Nat) : Nat := n

/-- The compiler can replace `slow` with this function. -/
def fast (n : Nat) : Nat := n

/-- Moving a compiler rule can change code generated for its users. -/
@[csimp] theorem compiler_rule : @slow = @fast := rfl

/-- Custom simplification sets are persistent attributes too. -/
@[placement_simp] theorem custom_simp_rule (n : Nat) : n + 0 = n := Nat.add_zero n

/-- A proposition supplies a nontrivial E-matching pattern for the tactic rule. -/
inductive Mark : Nat → Prop where
  /-- Every natural number has the marker. -/
  | mk (n : Nat) : Mark n

/-- A persistent tactic rule must not become a movable finding. -/
@[grind .] theorem grind_rule (n : Nat) : Mark n := Mark.mk n

/-- A structure supplies the type for extensionality and eliminator rules. -/
structure Box where
  /-- The sole field. -/
  value : Nat

/-- An extensionality rule is part of the environment an importer receives. -/
@[ext (iff := false)] theorem ext_rule (x y : Box) (h : x.value = y.value) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- Each eliminator attribute affects elaboration in importing modules. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
theorem eliminator_rule {motive : Box → Prop} (mk : ∀ n, motive ⟨n⟩) (x : Box) :
    motive x := by
  cases x
  exact mk _

/-- Unknown custom labels need the same conservative treatment. -/
@[placement_tag] theorem tagged_rule : True := True.intro

/-- Private names resolve through elaborator locations too. -/
@[placement_tag] private theorem private_rule : True := True.intro

/-- A scoped attribute on the declaration survives import. -/
@[scoped placement_tag] theorem scoped_declaration_rule : True := True.intro

/-- A local declaration attribute does not survive its enclosing section. -/
@[local placement_tag] theorem local_declaration_rule : True := True.intro

/-- A `simp` attribute does not hide another persistent attribute. -/
@[simp, placement_tag] theorem mixed_rule (n : Nat) : n + 0 = n := Nat.add_zero n

/-- An attribute command can register a theorem after its declaration. -/
theorem command_rule : True := True.intro

attribute [placement_tag] command_rule

/-- Scoped rules survive import even when their namespace is inactive. -/
theorem scoped_rule : True := True.intro

attribute [scoped placement_tag] scoped_rule

/-- A local rule does not survive the end of its section. -/
theorem local_rule : True := True.intro

section

attribute [local placement_tag] local_rule

end

/-- Attribute erasure is not an application of a persistent rule. -/
theorem erased_rule : True := True.intro

attribute [local placement_tag] erased_rule
attribute [-placement_tag] erased_rule

/-- An attribute on a definition cannot make a theorem movable. -/
@[placement_tag] def tagged_definition : Nat := 0

end CheckTheoremsAttributesTest

namespace CheckTheoremsAttributesTest

local infix:65 " ⋆⋆ " => Nat.add

/-- Local notation in a definition must not prevent attribute inspection. -/
def localValue (n : Nat) : Nat := n ⋆⋆ 0

/-- The declaration attribute still fails when the proof uses local notation. -/
@[placement_tag] theorem localSyntax_rule (n : Nat) : localValue n = n := Nat.add_zero n

/-- An unknown local symbol before a comment must not expose its contents as commands. -/
def localComment (n : Nat) : Nat := n ⋆⋆ /- attribute [not_an_attribute] unknown -/ 0

/-- This syntax token contains a literal parenthesis, rather than a grouping delimiter. -/
syntax "open(" : term

/-- Its expansion is irrelevant to attribute inspection. -/
macro_rules | `(open() => `(0)

/-- The token inside this quotation must not hide the subsequent real command. -/
def quoted : Lean.MacroM (Lean.TSyntax `term) := `(open()

/-- Nested interpolation literals must not hide later attribute commands. -/
def interpolation : String := s!"{ "`(" }"

/-- The command attribute is checked after the local symbols and quoted token. -/
theorem localCommand_rule : True := True.intro

attribute [placement_tag] localCommand_rule

/-- A proof using no constants can lack a declaration entry in the reference file. -/
@[placement_tag] theorem identity {p : Prop} (h : p) : p := h

-- An allowed documentation attribute must not hide the persistent custom label beside it.
@[inherit_doc tagged_rule, placement_tag] theorem metadata_mixed_rule : True := True.intro

end CheckTheoremsAttributesTest
