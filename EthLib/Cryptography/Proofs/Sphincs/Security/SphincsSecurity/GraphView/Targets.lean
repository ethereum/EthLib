module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Statement
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Correctness
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.RandomOracle
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Search
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Classification.Tree
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Domains

/-!
# Target sets of hash inputs

A cache is bad when some cached answer truncates into the target set of its input.

A table gives one target per address, and the target set of an input comes from its address.

A canonical input has an empty target set, so its own answer never makes the cache bad.
-/

@[expose] public section

section

/-! ### Bad caches -/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Security.CacheMatch

variable [Params]

open Completeness

attribute [local instance] Classical.propDecidable

/-- Some cached answer truncates into the target set of its input. -/
def Bad (targets : HashInput → Finset Digest) (cache : QueryCache HashSpec) : Prop :=
  ∃ input answer, cache input = some answer ∧ truncateHash answer ∈ targets input

end SphincsSecurity.Security.CacheMatch

end

section

/-! ### A target per address -/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Security.TargetAssignment

variable [Params]

open Concrete Completeness

attribute [local instance] Classical.propDecidable

/-- The input starts with the public parameter and the address bytes of the fields. -/
def atFields (parameter : PublicParameter) (input : HashInput) (fields : TweakFields) : Prop :=
  ∃ payload, input = bytesLE 16 parameter ++ fieldBytes fields ++ payload

omit [Params] in
theorem atFields_unique (parameter : PublicParameter) (input : HashInput)
    {left right : TweakFields} (hl : atFields parameter input left)
    (hr : atFields parameter input right) : left = right := by
  obtain ⟨l, hl⟩ := hl
  obtain ⟨r, hr⟩ := hr
  exact (fieldInput_injective (hl.symm.trans hr)).1

/-- The address fields at the start of an input, if it has any. -/
noncomputable def parseFields (parameter : PublicParameter) (input : HashInput) :
    Option TweakFields :=
  if h : ∃ fields, atFields parameter input fields then some h.choose else none

omit [Params] in
theorem parseFields_some_iff (parameter : PublicParameter) (input : HashInput)
    (fields : TweakFields) :
    parseFields parameter input = some fields ↔ atFields parameter input fields := by
  rw [parseFields]
  split
  · rename_i h
    rw [Option.some.injEq]
    constructor
    · rintro rfl; exact h.choose_spec
    · intro hf; exact atFields_unique parameter input h.choose_spec hf
  · rename_i h
    constructor
    · intro heq; cases heq
    · intro hf; exact False.elim (h ⟨fields, hf⟩)

theorem parseFields_tweakable (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    parseFields parameter (tweakableHashInput parameter domain payload) =
      some (hashDomainFields domain) :=
  (parseFields_some_iff _ _ _).2 ⟨payload, rfl⟩

/-- The target value at an address, with the canonical input there if there is one. -/
structure Entry where
  canonicalInput : Option HashInput
  value : Digest

abbrev Table := TweakFields → Option Entry

/-- The target set of an input: the value of its table entry, unless the input is canonical. -/
noncomputable def targets (parameter : PublicParameter) (table : Table)
    (input : HashInput) : Finset Digest :=
  match parseFields parameter input with
  | none => ∅
  | some fields => match table fields with
    | none => ∅
    | some entry => if entry.canonicalInput = some input then ∅ else {entry.value}

theorem targets_at_entry (parameter : PublicParameter) (table : Table) (domain : HashDomain)
    (payload : HashInput) (entry : Entry) (hentry : table (hashDomainFields domain) = some entry) :
    targets parameter table (tweakableHashInput parameter domain payload) =
      if entry.canonicalInput = some (tweakableHashInput parameter domain payload) then ∅
      else {entry.value} := by
  simp only [targets, parseFields_tweakable, hentry]

omit [Params] in
theorem canonical_input_excluded (parameter : PublicParameter) (table : Table) (input : HashInput)
    (fields : TweakFields) (entry : Entry) (hfields : atFields parameter input fields)
    (hentry : table fields = some entry) (hcanonical : entry.canonicalInput = some input) :
    targets parameter table input = ∅ := by
  simp only [targets, (parseFields_some_iff parameter input fields).2 hfields, hentry,
    hcanonical, ↓reduceIte]

end SphincsSecurity.Security.TargetAssignment

end
