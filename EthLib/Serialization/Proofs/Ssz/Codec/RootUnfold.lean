import EthLib.Serialization.Proofs.Ssz.Codec.RootLaws

/-! The root of a value, read off its layout with each nested value rooted on its own. -/

namespace EthLib.Serialization.Ssz

/-- The leaf one layout position contributes: a nested value's root, or the zero node for a gap. -/
def slotRoot : Option (Desc × Value) → Except Err Bytes
  | none => .ok zeroChunk
  | some (shape, value) => hashTreeRoot shape value

/-- The leaves of a layout: its packed nodes, or the roots of its nested values. -/
def leafChunks : Leaves → Except Err (Array Bytes)
  | .packed chunks => .ok chunks
  | .nested values => do return (← values.mapM slotRoot).toArray

/-- The root a layout gives over its leaves: the tree its capacity calls for, then the word it mixes in. -/
def finishLayout (layout : MerkleLayout) (chunks : Array Bytes) : Except Err Bytes := do
  let root ← match layout.limit with
    | none => .ok (merkleizeProgressiveUnchecked chunks.toList)
    | some capacity => merkleizeBoundedUnchecked chunks (some capacity)
  return match layout.mixin with
    | none => root
    | some word => mixIn root word

/-- Mapping two functions that agree on every element of a list gives the same result. -/
private theorem mapM_congr_mem {α β ε : Type} (f g : α → Except ε β) :
    ∀ (xs : List α), (∀ x ∈ xs, f x = g x) → xs.mapM f = xs.mapM g
  | [], _ => rfl
  | x :: xs, same => by
    -- The heads agree by assumption, and the tails by induction.
    simp only [List.mapM_cons]
    rw [same x (by simp), mapM_congr_mem f g xs fun y member => same y (by simp [member])]

/-- The root of a value is its layout's root, each nested value rooted on its own budget. -/
theorem hashTreeRoot_unfold (shape : Desc) (value : Value) :
    hashTreeRoot shape value = (do
      let layout ← merkleLayout shape value
      finishLayout layout (← leafChunks layout.leaves)) := by
  -- Every type nests at least one level, so the root spends one budget step on the layout.
  have positive : 0 < shape.nesting := by cases shape <;> simp [Desc.nesting]
  obtain ⟨budget, eq⟩ : ∃ budget, shape.nesting = budget + 1 := ⟨shape.nesting - 1, by omega⟩
  rw [hashTreeRoot, eq, hashTreeRootAt]
  cases layoutEq : merkleLayout shape value with
  | error e => rfl
  | ok layout =>
    simp only [Bind.bind, Except.bind]
    rcases layout with ⟨leaves, limit, mixin⟩
    cases leaves with
    | packed chunks =>
      simp only [layoutChunksAt, leafChunks, Leaves.count, pure, Except.pure, Option.getD_none,
        Array.extract_size, finishLayout, Bind.bind, Except.bind]
      cases limit with
      | none => cases mixin <;> rfl
      | some c => cases merkleizeBoundedUnchecked chunks (some c) <;> cases mixin <;> rfl
    | nested values =>
      simp only [layoutChunksAt, leafChunks, Leaves.count, List.drop_zero, Nat.sub_zero, Option.getD_none,
        List.take_length, Bind.bind, Except.bind, pure, Except.pure]
      -- Each nested value has a smaller nesting, which the remaining budget covers.
      rw [mapM_congr_mem _ slotRoot values ?same]
      case same =>
        intro slot member
        match slot with
        | none => rfl
        | some (child, inner) =>
          have := merkleLayout_child_nesting shape value _ layoutEq values rfl child inner member
          exact hashTreeRootAt_eq_hashTreeRoot child inner budget (by omega)
      cases values.mapM slotRoot with
      | error e => rfl
      | ok rs =>
        simp only [finishLayout, Bind.bind, Except.bind, pure, Except.pure]
        cases limit with
        | none => cases mixin <;> rfl
        | some c => cases merkleizeBoundedUnchecked rs.toArray (some c) <;> cases mixin <;> rfl

end EthLib.Serialization.Ssz
