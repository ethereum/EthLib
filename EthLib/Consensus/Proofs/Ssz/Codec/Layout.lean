import EthLib.Consensus.Ssz.Codec.Layout
import EthLib.Consensus.Proofs.Ssz.Merkle.Tree

/-! Laws of the layout that places a progressive container's fields around its gaps. -/

namespace EthLib.Consensus.Ssz

/-- A successful layout preserves every field in order and has one slot per position. -/
private theorem placeSlots_preserves {active : List Bool} {fields : List (Desc × Value)}
    {slots : List (Option (Desc × Value))} (placed : placeSlots active fields = .ok slots) :
    slots.filterMap id = fields ∧ slots.length = active.length := by
  induction active generalizing fields slots with
  | nil =>
    -- With no positions left, success requires no fields left either.
    cases fields <;> simp_all [placeSlots]
  | cons bit active ih =>
    cases bit with
    | false =>
      -- Removing a gap keeps the field sequence and shortens the layout by one.
      cases tail : placeSlots active fields <;>
        simp [placeSlots, tail, Bind.bind, Except.bind, pure, Except.pure] at placed
      subst slots
      simpa using ih tail
    | true =>
      -- An occupied position keeps the first field and delegates the remaining positions.
      cases fields with
      | nil => simp [placeSlots] at placed
      | cons field fields =>
        cases tail : placeSlots active fields <;>
          simp [placeSlots, tail, Bind.bind, Except.bind, pure, Except.pure] at placed
        subst slots
        obtain ⟨ordered, sized⟩ := ih tail
        simp [ordered, sized]

/-- Removing gaps from a successful layout recovers the declared fields in order. -/
theorem placeSlots_fields {active : List Bool} {fields : List (Desc × Value)}
    {slots : List (Option (Desc × Value))} (placed : placeSlots active fields = .ok slots) :
    slots.filterMap id = fields :=
  -- Field preservation follows independently of the number of gaps.
  (placeSlots_preserves placed).1

end EthLib.Consensus.Ssz
