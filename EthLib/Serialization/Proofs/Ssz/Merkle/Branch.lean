import EthLib.Serialization.Ssz.Merkle.Verify
import EthLib.Serialization.Proofs.Ssz.Merkle.Gindex
import EthLib.Cryptography.Proofs.Merkle.Binding

/-! Climbing an SSZ branch is folding a path of the generic Merkle tree. -/

namespace EthLib.Serialization.Ssz

/-- Climbing one more node adds one hash at the top of the climb. -/
theorem climbBranch_append (index : Nat) : ∀ (level : Nat) (node last : Bytes)
    (siblings : List Bytes), climbBranch index level node (siblings ++ [last]) =
      if gindexBit index (level + siblings.length)
      then combine last (climbBranch index level node siblings)
      else combine (climbBranch index level node siblings) last
  | _, _, _, [] => by simp [climbBranch]
  | level, node, last, sibling :: rest => by
    simp only [List.cons_append, climbBranch, List.length_cons]
    rw [climbBranch_append index (level + 1)]
    simp [Nat.add_assoc, Nat.add_comm 1]

/--
A branch climbed from its leaf is the generic Merkle fold of that leaf, with the branch as its path.

The fold's node hash is `combine` at every position, and the generalized index is the leaf index.

So the generic statements about folds, such as binding, hold for SSZ branches too.
-/
theorem climbBranch_eq_fold (index : Nat) (leaf : Bytes) (proof : List Bytes) :
    climbBranch index 0 leaf proof
      = Cryptography.Merkle.fold (height := proof.length) (fun _ _ => combine) index leaf
          ⟨proof.toArray, rfl⟩ := by
  -- Climbing the first `k` siblings is the generic climb of `k` levels.
  have climbed : ∀ k (hk : k ≤ proof.length),
      Cryptography.Merkle.Internal.climbUpto (height := proof.length) (fun _ _ => combine) index
          ⟨proof.toArray, rfl⟩ leaf k hk
        = climbBranch index 0 leaf (proof.take k) := by
    intro k
    induction k with
    | zero => intro _; simp [climbBranch, Cryptography.Merkle.Internal.climbUpto]
    | succ k ih =>
      intro hk
      -- The first `k + 1` siblings are the first `k`, then sibling `k`.
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
        climbBranch_append, Cryptography.Merkle.Internal.climbUpto, ← ih (by omega)]
      simp only [Cryptography.Merkle.Internal.climbStep, List.length_take,
        Nat.min_eq_left (show k ≤ proof.length by omega), Nat.zero_add, gindexBit_parity]
      -- Bit `k` of the index says which side the sibling joins on, in both climbs.
      rcases Nat.mod_two_eq_zero_or_one (index >>> k) with bit | bit <;> simp [bit]
  rw [Cryptography.Merkle.fold, climbed proof.length (Nat.le_refl _), List.take_length]

end EthLib.Serialization.Ssz
