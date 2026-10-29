import EthLib.Serialization.Ssz.Codec.Layout

/-! Leaf shapes record the positions and types needed to align commitments. -/

namespace EthLib.Serialization.Ssz

/-- The number of packed nodes, or the type and presence of each nested position. -/
def Leaves.shapes : Leaves → Sum Nat (List (Option Desc))
  -- Packed leaves need only a node count to align their byte positions.
  | .packed chunks => .inl chunks.size
  -- Nested leaves retain their declared types and gaps while forgetting their values.
  | .nested slots => .inr (slots.map (Option.map Prod.fst))

/-- Equal leaf shapes have the same number of materialized positions. -/
theorem Leaves.count_of_shapes {left right : Leaves} (same : left.shapes = right.shapes) :
    left.count = right.count := by
  -- Packed shapes state their count directly, while nested shapes retain one entry per position.
  cases left <;> cases right <;> simp [shapes, Leaves.count] at same ⊢
  · exact same
  · simpa using congrArg List.length same

end EthLib.Serialization.Ssz
