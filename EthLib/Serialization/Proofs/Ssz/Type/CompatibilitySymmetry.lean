import EthLib.Serialization.Proofs.Ssz.Type.Equality

/-! Tree-shape compatibility is symmetric at every comparison depth. -/

namespace EthLib.Serialization.Ssz

private theorem fieldsCompatible_symm {budget : Nat}
    (inner : ∀ left right, compatibleAt budget left right = compatibleAt budget right left) :
    ∀ left right, fieldsCompatible budget left right = fieldsCompatible budget right left := by
  -- Reversing a field comparison preserves each aligned pair and simultaneous list termination.
  intro left
  induction left <;> intro right <;> cases right <;> simp [fieldsCompatible, *]

/-- Checking one option against a list checks it against each. -/
theorem optionAgainstAll_iff (budget : Nat) (option : Desc) (options : List Desc) :
    optionAgainstAll budget option options = true ↔
      ∀ other ∈ options, compatibleAt budget option other = true := by
  -- Checking one option against a list means checking every member of that list.
  induction options <;> simp [optionAgainstAll, *]

/-- Two unions' options agree when each of one is compatible with each of the other. -/
theorem unionOptionsAgree_iff (budget : Nat) (left right : List Desc) :
    unionOptionsAgree budget left right = true ↔
      ∀ one ∈ left, ∀ other ∈ right, compatibleAt budget one other = true := by
  -- Each option on the left must agree with every option on the right.
  induction left <;> simp [unionOptionsAgree, optionAgainstAll_iff, *]

private theorem unionOptionsAgree_symm {budget : Nat}
    (inner : ∀ left right, compatibleAt budget left right = compatibleAt budget right left)
    (left right : List Desc) :
    unionOptionsAgree budget left right = unionOptionsAgree budget right left := by
  -- Swapping the two finite quantifiers preserves the set of option pairs being checked.
  apply Bool.eq_iff_iff.mpr
  simp only [unionOptionsAgree_iff]
  constructor <;> intro all one oneIn other otherIn <;> rw [inner] <;> exact all other otherIn one oneIn

private theorem layoutPairAgree_symm {budget : Nat}
    (inner : ∀ left right, compatibleAt budget left right = compatibleAt budget right left)
    (leftFields rightFields : List Desc) (left right : Nat × String × Nat) :
    layoutPairAgree budget leftFields rightFields left right =
      layoutPairAgree budget rightFields leftFields right left := by
  -- Compare shared positions separately from distinct positions, since they enforce different rules.
  conv => lhs; rw [layoutPairAgree.eq_def]
  conv => rhs; rw [layoutPairAgree.eq_def]
  rcases left with ⟨position, name, ordinal⟩
  rcases right with ⟨otherPosition, otherName, otherOrdinal⟩
  by_cases same : position = otherPosition
  -- At a shared position, both field lookups must succeed and their types must agree symmetrically.
  · subst otherPosition
    cases leftFields[ordinal]? <;> cases rightFields[otherOrdinal]? <;>
      apply Bool.eq_iff_iff.mpr <;> simp [inner]
    simp only [eq_comm, implies_true]
  -- At distinct positions, rejecting a repeated field name is symmetric.
  · apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, same, ↓reduceIte, bne_iff_ne, ne_eq, Ne.symm same]
    exact not_congr eq_comm

private theorem layoutsAgree_symm {budget : Nat}
    (inner : ∀ left right, compatibleAt budget left right = compatibleAt budget right left)
    (leftActive rightActive : List Bool) (leftNames rightNames : List String)
    (leftFields rightFields : List Desc) :
    layoutsAgree budget leftActive leftNames leftFields rightActive rightNames rightFields =
      layoutsAgree budget rightActive rightNames rightFields leftActive leftNames leftFields := by
  -- Every cross-layout field pair is checked in both orders.
  apply Bool.eq_iff_iff.mpr
  simp only [layoutsAgree, List.all_eq_true]
  constructor <;> intro all left leftIn right rightIn <;> rw [layoutPairAgree_symm inner] <;>
    exact all right rightIn left leftIn

/-- Swapping the two declarations preserves compatibility, including at a finite comparison budget. -/
theorem compatibleAt_symm (budget : Nat) :
    ∀ left right, compatibleAt budget left right = compatibleAt budget right left := by
  -- Each descent consumes one comparison level on both sides.
  induction budget with
  | zero => intro left right; simp [compatibleAt.eq_def]
  | succ budget ih =>
    intro left right
    -- Identical declarations are recognized before any nested compatibility check.
    by_cases same : left = right
    · subst right
      rfl
    · conv => lhs; rw [compatibleAt.eq_def]
      conv => rhs; rw [compatibleAt.eq_def]
      dsimp only
      simp only [show (left == right) = false by simp [same],
        show (right == left) = false by simp [Ne.symm same], Bool.false_eq_true, ite_false]
      -- Byte-array aliases normalize before the remaining constructors are compared.
      cases leftBytes : left.byteSequence <;> cases rightBytes : right.byteSequence
      all_goals dsimp only
      all_goals try (apply Bool.eq_iff_iff.mpr; simp; exact eq_comm)
      all_goals try rfl
      -- Nested lists, layouts, and union options inherit symmetry from the smaller comparison budget.
      cases left <;> cases right <;> apply Bool.eq_iff_iff.mpr <;>
        simp [fieldsCompatible_symm ih, unionOptionsAgree_symm ih, layoutsAgree_symm ih, ih] <;>
        simp only [eq_comm, implies_true]

/-- Tree-shape compatibility is symmetric, even for declarations not yet validated. -/
theorem isCompatible_symm (left right : Desc) :
    isCompatible left right = isCompatible right left := by
  -- The sum of the two nesting depths is unchanged when the declarations are swapped.
  unfold isCompatible
  rw [Nat.add_comm, compatibleAt_symm]

/-- Compatible layouts keep every shared field name at the same tree position. -/
theorem layoutsAgree_name_position {budget : Nat} {leftActive rightActive : List Bool}
    {leftNames rightNames : List String} {leftFields rightFields : List Desc}
    (agree : layoutsAgree budget leftActive leftNames leftFields
      rightActive rightNames rightFields = true)
    {left right : Nat × String × Nat}
    (leftIn : left ∈ placedOrdinals leftActive leftNames)
    (rightIn : right ∈ placedOrdinals rightActive rightNames)
    (named : left.2.1 = right.2.1) : left.1 = right.1 := by
  rw [layoutsAgree.eq_def] at agree
  -- The selected pair inherits the condition imposed on every cross-layout field pair.
  have pair := List.all_eq_true.mp (List.all_eq_true.mp agree left leftIn) right rightIn
  -- A repeated field name at different positions would violate compatibility.
  exact Classical.byContradiction fun same => by simp [layoutPairAgree, same, named] at pair

/-- A shared tree position carries one field name and compatible field types. -/
theorem layoutsAgree_shared_position {budget : Nat} {leftActive rightActive : List Bool}
    {leftNames rightNames : List String} {leftFields rightFields : List Desc}
    (agree : layoutsAgree budget leftActive leftNames leftFields
      rightActive rightNames rightFields = true)
    {left right : Nat × String × Nat}
    (leftIn : left ∈ placedOrdinals leftActive leftNames)
    (rightIn : right ∈ placedOrdinals rightActive rightNames)
    (position : left.1 = right.1) :
    left.2.1 = right.2.1 ∧ ∃ leftType rightType,
      leftFields[left.2.2]? = some leftType ∧ rightFields[right.2.2]? = some rightType ∧
      compatibleAt budget leftType rightType = true := by
  rw [layoutsAgree.eq_def] at agree
  -- The selected pair inherits the condition imposed on every cross-layout field pair.
  have pair := List.all_eq_true.mp (List.all_eq_true.mp agree left leftIn) right rightIn
  -- A shared position cannot be compatible if either declared field type is missing.
  cases leftType : leftFields[left.2.2]? <;> cases rightType : rightFields[right.2.2]? <;>
    simp_all [layoutPairAgree]

end EthLib.Serialization.Ssz
