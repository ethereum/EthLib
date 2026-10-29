import EthLib.Consensus.Proofs.Ssz.Type.CompatibilitySymmetry
import EthLib.Consensus.Proofs.Ssz.Codec.LayoutLaws

/-! Compatibility gives the same verdict at every budget that covers the left type's nesting. -/

namespace EthLib.Consensus.Ssz

/-- Field lists compare alike at two budgets that compare each left field alike. -/
theorem fieldsCompatible_congr {budget budget' : Nat} : ∀ left right : List Desc,
    (∀ x ∈ left, ∀ y, compatibleAt budget x y = compatibleAt budget' x y) →
      fieldsCompatible budget left right = fieldsCompatible budget' left right
  | [], [], _ => by simp [fieldsCompatible]
  | x :: left, y :: right, same => by
    -- The heads compare alike by assumption, and the tails by induction.
    simp [fieldsCompatible, same x (by simp),
      fieldsCompatible_congr left right (fun x member => same x (by simp [member]))]
  | [], _ :: _, _ | _ :: _, [], _ => by simp [fieldsCompatible]

/-- Union options compare alike at two budgets that compare each left option alike. -/
theorem unionOptionsAgree_congr {budget budget' : Nat} (left right : List Desc)
    (same : ∀ x ∈ left, ∀ y, compatibleAt budget x y = compatibleAt budget' x y) :
    unionOptionsAgree budget left right = unionOptionsAgree budget' left right := by
  -- Both sides check every pair of options, and each pair compares alike.
  apply Bool.eq_iff_iff.mpr
  simp only [unionOptionsAgree_iff]
  constructor <;> intro all x hx y hy
  · rw [← same x hx y]; exact all x hx y hy
  · rw [same x hx y]; exact all x hx y hy

/-- Layouts compare alike at two budgets that compare each left field alike. -/
theorem layoutsAgree_congr {budget budget' : Nat} (leftActive rightActive : List Bool)
    (leftNames rightNames : List String) (leftFields rightFields : List Desc)
    (same : ∀ x ∈ leftFields, ∀ y, compatibleAt budget x y = compatibleAt budget' x y) :
    layoutsAgree budget leftActive leftNames leftFields rightActive rightNames rightFields =
      layoutsAgree budget' leftActive leftNames leftFields rightActive rightNames rightFields := by
  rw [layoutsAgree.eq_def, layoutsAgree.eq_def]
  congr 1; funext x; congr 1; funext y
  rw [layoutPairAgree.eq_def, layoutPairAgree.eq_def]
  -- Only a shared position compares fields, and those fields are the left layout's.
  cases g : leftFields[x.2.2]? with
  | none => simp
  | some f => cases rightFields[y.2.2]? <;> simp [same f (List.mem_of_getElem? g)]

/-- Compatibility answers alike at any two budgets at least the left type's nesting. -/
theorem compatibleAt_stable : ∀ (budget budget' : Nat) (left right : Desc),
    left.nesting ≤ budget → left.nesting ≤ budget' →
      compatibleAt budget left right = compatibleAt budget' left right := by
  intro b
  induction b with
  | zero => intro _ l _ h; have := Desc.nesting_pos l; omega
  | succ b ih =>
    intro b' l r h h'
    obtain ⟨b', rfl⟩ : ∃ c, b' = c + 1 := ⟨b' - 1, by have := Desc.nesting_pos l; omega⟩
    -- Each descent lands on a type at least one level shallower, within both smaller budgets.
    have child : ∀ x, x.nesting + 1 ≤ l.nesting → ∀ y, compatibleAt b x y = compatibleAt b' x y :=
      fun x hx y => ih b' x y (by omega) (by omega)
    rw [compatibleAt.eq_def, compatibleAt.eq_def]
    cases l <;> cases r <;> try rfl
    case vector.vector e _ _ _ | list.list e _ _ _ =>
      simp only [child e (by simp [Desc.nesting])]
    case progressiveList.progressiveList e _ _ _ =>
      simp only [child e (by simp [Desc.nesting])]
    case container.container _ fs _ _ =>
      simp only [fieldsCompatible_congr (budget := b) (budget' := b') fs _
        (fun x hx => child x (by have := nesting_le_deepest x fs hx; simp [Desc.nesting]; omega))]
    case progressiveContainer.progressiveContainer la _ fs _ _ _ =>
      simp only [layoutsAgree_congr (budget := b) (budget' := b') la _ _ _ fs _
        (fun x hx => child x (by have := nesting_le_deepest x fs hx; simp [Desc.nesting]; omega))]
    case compatibleUnion.compatibleUnion _ os _ _ =>
      simp only [unionOptionsAgree_congr (budget := b) (budget' := b') os _
        (fun x hx => child x (by have := nesting_le_deepest x os hx; simp [Desc.nesting]; omega))]

end EthLib.Consensus.Ssz
