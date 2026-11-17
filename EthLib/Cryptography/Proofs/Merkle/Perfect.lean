module

public import EthLib.Cryptography.Proofs.Merkle.Completeness
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Option
import Mathlib.Data.Nat.Bitwise

/-!
# Proofs: the Merkle tree as the oracle framework's perfect tree

The oracle framework that these proofs import has its own perfect Merkle tree.

It computes a node, a path and a climb with the same recursion as this library.

Here each of the three equals its counterpart.

A node is equal in every monad, and a path and a climb in every lawful monad.

So a theorem proved about one tree carries over to the other through these equations.

This library passes the position of a node to its hash, and the framework its height and index.

Both make the hash calls in the same order, so a bound on the calls also carries over.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle

variable {m : Type → Type} [Monad m] {α : Type} (hash : Position → α → α → m α)

/-- The framework's sibling of a node is the node with the low bit of its index flipped.

The framework adds or subtracts 1 by parity, and this library flips the low bit.

The two agree on every index. -/
theorem sibling_eq_xor_one (j : Nat) : PerfectMerkleTree.sibling j = j ^^^ 1 := by
  unfold PerfectMerkleTree.sibling
  split
  · -- An even index gains 1, which sets its low bit.
    exact (Nat.xor_one_of_even (Nat.even_iff.mpr ‹_›)).symm
  · -- An odd index loses 1, which clears its low bit.
    exact (Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))).symm

/-- A node is the framework's root of the subtree at the same height and index.

The framework's hash takes a height and an index, which together are a position here. -/
theorem node_eq_merkleRootM (leaves : Nat → m α) :
    ∀ p : Position, node hash leaves p
      = PerfectMerkleTree.merkleRootM leaves (fun level j => hash ⟨level, j⟩) p.level p.index := by
  rintro ⟨level, j⟩
  induction level generalizing j with
  | zero => rfl
  -- Both trees hash their two subtrees, left first, so they agree level by level.
  | succ level ih => simp only [node_succ, PerfectMerkleTree.merkleRootM, ih]

/-- The root of a tree is the framework's root of the subtree at index 0. -/
theorem root_eq_merkleRootM (leaves : Nat → m α) (h : Nat) :
    root hash leaves h
      = PerfectMerkleTree.merkleRootM leaves (fun level j => hash ⟨level, j⟩) h 0 :=
  node_eq_merkleRootM hash leaves ⟨h, 0⟩

variable [LawfulMonad m]

/-- The siblings of `n + 1` nodes are those of the first `n`, then one more at the end.

This library puts the lowest sibling first and recurses upward.

The framework builds the path of height `n + 1` from that of height `n` and appends the top sibling.

This equation turns the first order into the second. -/
theorem siblings_succ_push (leaves : Nat → m α) :
    ∀ (n : Nat) (p : Position),
      siblings hash leaves p (n + 1)
        = do
          let rest ← siblings hash leaves p n
          let sibling ← node hash leaves (p.ancestor n).sibling
          return rest.push sibling
  | 0, p => by
    -- With one sibling, both sides compute the sibling of the node itself.
    simp only [siblings, bind_pure_comp, map_pure, Position.ancestor_zero]
    rw [pure_bind]
    congr 1
  | n + 1, p => by
    -- Take off the lowest sibling, and apply the equation to the siblings of the parent.
    conv_lhs => rw [siblings, siblings_succ_push leaves n p.parent]
    conv_rhs => rw [siblings]
    simp only [bind_assoc, pure_bind, Position.ancestor_parent]
    refine bind_congr fun first => bind_congr fun rest => bind_congr fun last => ?_
    congr 1
    apply Vector.ext
    intro i hi
    -- Entry 0 is the first sibling, the last entry is the new one, and the rest lie between.
    simp [Vector.getElem_push, Vector.getElem_append]
    split_ifs <;> simp_all <;> omega

/-- A path is the framework's path that keeps its length in its type.

Both are vectors of `h` siblings, from the leaf up. -/
theorem path_eq_intrinsicAuthPathM (leaves : Nat → m α) (j : Nat) :
    ∀ h, path hash leaves h j
      = PerfectMerkleTree.intrinsicAuthPathM leaves (fun level j => hash ⟨level, j⟩) j h
  | 0 => rfl
  | h + 1 => by
    -- Both paths of height `h + 1` are the path of height `h`, then the top sibling.
    rw [path, siblings_succ_push, ← path, path_eq_intrinsicAuthPathM leaves j h]
    simp only [PerfectMerkleTree.intrinsicAuthPathM, sibling_eq_xor_one, node_eq_merkleRootM,
      Position.sibling_level, Position.sibling_index, Position.ancestor_level,
      Position.ancestor_index, Nat.zero_add]

/-- A path, as a list, is the framework's path as a list. -/
theorem path_toList_eq_authPathM (leaves : Nat → m α) (j h : Nat) :
    (fun s => s.toList) <$> path hash leaves h j
      = PerfectMerkleTree.authPathM leaves (fun level j => hash ⟨level, j⟩) j h := by
  rw [path_eq_intrinsicAuthPathM, PerfectMerkleTree.intrinsicAuthPathM_toList]

/-- A climb from a node is the framework's climb, with every height shifted up by its level.

The framework's climb counts heights from its starting node.

This library counts levels from the leaves, so a climb from level `l` hashes at heights plus `l`. -/
theorem climb_eq_climbM_shift :
    ∀ (siblings : List α) (p : Position) (current : α),
      climb hash p current siblings
        = PerfectMerkleTree.climbM (fun height index => hash ⟨height + p.level, index⟩) p.index
            current siblings
  | [], _, _ => rfl
  | sibling :: rest, p, current => by
    -- Unfold one step on each side, and match the rest of the climb one level up.
    rw [PerfectMerkleTree.climbM_cons, climb]
    simp only [climb_eq_climbM_shift rest p.parent, Position.parent_level, Position.parent_index,
      ← Nat.add_assoc, Nat.add_right_comm _ 1 p.level]
    -- Both put the held node on the left exactly when its index is even.
    rw [ordered_eq_ite]
    split <;> simp_all <;> rfl

/-- A climb from a leaf is the framework's climb, with no shift since leaves are at level 0. -/
theorem climb_eq_climbM (j : Nat) (current : α) (siblings : List α) :
    climb hash ⟨0, j⟩ current siblings
      = PerfectMerkleTree.climbM (fun level j => hash ⟨level, j⟩) j current siblings := by
  rw [climb_eq_climbM_shift]
  rfl

end EthLib.Cryptography.Merkle
