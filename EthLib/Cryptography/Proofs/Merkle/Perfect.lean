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

Both trees pass the height and the index of a node to its hash.

Both make the hash calls in the same order, so a bound on the calls also carries over.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle

variable {m : Type → Type} [Monad m] {α : Type} (hash : Nat → Nat → α → α → m α)

/-- The framework's sibling of a node is the node with the low bit of its index flipped. -/
theorem sibling_eq_xor_one (j : Nat) : PerfectMerkleTree.sibling j = j ^^^ 1 := by
  unfold PerfectMerkleTree.sibling
  split
  · exact (Nat.xor_one_of_even (Nat.even_iff.mpr ‹_›)).symm
  · exact (Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))).symm

/-- A node is the framework's root of the subtree at the same height and index. -/
theorem node_eq_merkleRootM (leaves : Nat → m α) :
    ∀ level j, node hash leaves level j = PerfectMerkleTree.merkleRootM leaves hash level j
  | 0, _ => rfl
  | level + 1, j => by
    simp only [node, PerfectMerkleTree.merkleRootM, node_eq_merkleRootM leaves level]

/-- The root of a tree is the framework's root of the subtree at index 0. -/
theorem root_eq_merkleRootM (leaves : Nat → m α) (h : Nat) :
    root hash leaves h = PerfectMerkleTree.merkleRootM leaves hash h 0 :=
  node_eq_merkleRootM hash leaves h 0

variable [LawfulMonad m]

/-- The siblings of `n + 1` nodes are those of the first `n`, then one more at the end. -/
theorem siblings_succ_push (leaves : Nat → m α) :
    ∀ n level j,
      siblings hash leaves level j (n + 1)
        = do
          let rest ← siblings hash leaves level j n
          let sibling ← node hash leaves (level + n) ((j / 2 ^ n) ^^^ 1)
          return rest.push sibling
  | 0, level, j => by
    simp only [siblings, bind_pure_comp, map_pure, Nat.add_zero, Nat.pow_zero, Nat.div_one]
    rw [pure_bind]
    congr 1
  | n + 1, level, j => by
    conv_lhs => rw [siblings, siblings_succ_push leaves n (level + 1) (j / 2)]
    conv_rhs => rw [siblings]
    simp only [bind_assoc, pure_bind, div_two_div_pow, Nat.add_right_comm level 1 n,
      Nat.add_assoc]
    refine bind_congr fun first => bind_congr fun rest => bind_congr fun last => ?_
    congr 1
    apply Vector.ext
    intro i hi
    -- Entry 0 is the first sibling, the last entry is the new one, and the rest lie between.
    simp [Vector.getElem_push, Vector.getElem_append]
    split_ifs <;> simp_all <;> omega

/-- A path is the framework's path that keeps its length in its type. -/
theorem path_eq_intrinsicAuthPathM (leaves : Nat → m α) (j : Nat) :
    ∀ h, path hash leaves h j = PerfectMerkleTree.intrinsicAuthPathM leaves hash j h
  | 0 => rfl
  | h + 1 => by
    rw [path, siblings_succ_push, ← path, path_eq_intrinsicAuthPathM leaves j h]
    simp only [PerfectMerkleTree.intrinsicAuthPathM, Nat.zero_add, sibling_eq_xor_one,
      node_eq_merkleRootM]

/-- A path, as a list, is the framework's path. -/
theorem path_toList_eq_authPathM (leaves : Nat → m α) (j h : Nat) :
    (fun s => s.toList) <$> path hash leaves h j
      = PerfectMerkleTree.authPathM leaves hash j h := by
  rw [path_eq_intrinsicAuthPathM, PerfectMerkleTree.intrinsicAuthPathM_toList]

/-- A climb from level `level` is the framework's climb, with every height shifted up by `level`. -/
theorem climb_eq_climbM_shift :
    ∀ (siblings : List α) (level j : Nat) (current : α),
      climb hash level j current siblings
        = PerfectMerkleTree.climbM (fun height index => hash (height + level) index) j current
            siblings
  | [], _, _, _ => rfl
  | sibling :: rest, level, j, current => by
    rw [PerfectMerkleTree.climbM_cons, climb]
    simp only [climb_eq_climbM_shift rest (level + 1), Nat.add_assoc, Nat.add_comm 1 level]
    unfold ordered
    split <;> rfl

/-- A climb from a leaf is the framework's climb. -/
theorem climb_eq_climbM (j : Nat) (current : α) (siblings : List α) :
    climb hash 0 j current siblings = PerfectMerkleTree.climbM hash j current siblings := by
  rw [climb_eq_climbM_shift]
  rfl

end EthLib.Cryptography.Merkle
