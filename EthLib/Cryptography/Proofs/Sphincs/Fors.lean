module

public import EthLib.Cryptography.Sphincs.Fors
public import EthLib.Cryptography.Proofs.Sphincs.Tree

/-!
# Proofs: `Sphincs.Fors`

An honest FORS opening leads back to the instance's FORS key.

- Climbing levels 0 to 8 from leaf `l` reaches `Y_{9, floor(l / 512)}`.
- The last path node is the other one, `Y_{9, floor(l / 512) xor 1}`.
- Bit 9 of `l` puts the two in order, which gives `(Y_{9,0}, Y_{9,1})`.

Each step specializes a statement proved for every Merkle tree.

A FORS tree hashes only at levels 1 to 9, so its node addresses hold the true level and index.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

variable {pp : PublicParam} {seed : Seed} {idx : Nat} {kappa : Fin FORS_TREES}

/-! ## Unfolding a node -/

/-- Every FORS node above level 0 is the hash of its two children. -/
theorem forsNode_succ (l j : Nat) :
    forsNode pp seed idx kappa (l + 1) j
      = forsNodeHash pp idx kappa (l + 1) j (forsNode pp seed idx kappa l (2 * j))
          (forsNode pp seed idx kappa l (2 * j + 1)) :=
  rfl

/-- A leaf index is its own position. -/
theorem forsIndex_val (l : Fin (2 ^ FORS_HEIGHT)) : forsIndex l.val = l :=
  Fin.ext (Nat.mod_eq_of_lt l.isLt)

/-- On levels up to 15 and indices below `2^10`, the node hash reads its position exactly. -/
theorem forsNodeHash_of_lt {level j : Nat} (hlevel : level < 16) (hj : j < 2 ^ FORS_HEIGHT)
    (left right : Digest) :
    forsNodeHash pp idx kappa level j left right
      = th pp (addrForsNode idx kappa ⟨level, hlevel⟩ ⟨j, hj⟩) (packBytes left ++ packBytes right) := by
  simp only [forsNodeHash, Fin.ofNat, forsIndex, Nat.mod_eq_of_lt hlevel, Nat.mod_eq_of_lt hj]

/-- A node up to level 9 is the same with any node hash that agrees on levels 1 to 9. -/
theorem forsNode_eq_of_agree (hash' : Nat → Nat → Digest → Digest → Id Digest)
    (agree : ∀ k, 1 ≤ k → k < FORS_HEIGHT → forsNodeHash pp idx kappa k = hash' k)
    {level : Nat} (hlevel : level < FORS_HEIGHT) (j : Nat) :
    forsNode pp seed idx kappa level j = (Merkle.node hash' (forsLeaves pp seed idx kappa) level j).run := by
  rw [forsNode, Merkle.node_congr _ hash' _ level j fun k h1 h2 => agree k h1 (by omega)]

/-- An opening's path is the same with any node hash that agrees on levels 1 to 9. -/
theorem treeOpen_path_eq_of_agree (hash' : Nat → Nat → Digest → Digest → Id Digest)
    (agree : ∀ k, 1 ≤ k → k < FORS_HEIGHT → forsNodeHash pp idx kappa k = hash' k)
    (l : Fin (2 ^ FORS_HEIGHT)) :
    (treeOpen pp seed idx kappa l).path
      = (Merkle.path hash' (forsLeaves pp seed idx kappa) FORS_HEIGHT l).run := by
  rw [treeOpen, Merkle.path_congr _ hash' _ _ _ agree]

/-- The leaf an opening reveals is the honest level-0 node. -/
theorem forsLeafHash_forsSecret (l : Fin (2 ^ FORS_HEIGHT)) :
    forsLeafHash pp idx kappa l (forsSecret pp seed idx kappa l) = forsNode pp seed idx kappa 0 l.val := by
  simp only [forsNode, Merkle.node, forsLeaves, forsIndex_val]
  rfl

/-! ## An honest opening leads to the FORS key -/

/-- An honest opening of one tree recovers the tree's two level-9 nodes, in order. -/
theorem treeRecover_treeOpen (l : Fin (2 ^ FORS_HEIGHT)) :
    treeRecover pp idx kappa l (treeOpen pp seed idx kappa l)
      = (forsNode pp seed idx kappa (FORS_HEIGHT - 1) 0, forsNode pp seed idx kappa (FORS_HEIGHT - 1) 1) := by
  simp only [treeRecover, treeOpen, forsLeafHash_forsSecret]
  -- Bit 9 of `l` is the low bit of `floor(l / 2^9)`.
  rw [Nat.shiftRight_eq_div_pow]
  -- The climb reaches one level-9 node, and the last path node is the other one, in order.
  rw [show forsNode pp seed idx kappa 0 l.val = (forsLeaves pp seed idx kappa l.val).run from rfl,
    Merkle.ordered_climb_path_last _ _ (by decide)]
  -- A leaf below `2^10` has a level-9 ancestor of index 0 or 1, so their parent is node 0.
  have hl : l.val < 1024 := l.isLt
  have hparent : l.val / 2 ^ (FORS_HEIGHT - 1) / 2 = 0 := by
    show l.val / 512 / 2 = 0
    omega
  rw [hparent]
  rfl

/-- Honest openings of every tree recover the instance's FORS key. -/
theorem forsRecover_forsSign (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES) :
    forsRecover pp idx leaves (forsSign pp seed idx leaves) = forsKey pp seed idx := by
  -- Tree by tree, the opening recovers the tree's part of the key.
  unfold forsRecover forsSign forsKey
  refine Vector.ext fun k hk => ?_
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  have hopen : (Vector.ofFn fun kappa => treeOpen pp seed idx kappa leaves[kappa])[(⟨k, hk⟩ : Fin _)]
      = treeOpen pp seed idx ⟨k, hk⟩ leaves[(⟨k, hk⟩ : Fin _)] := by
    rw [Fin.getElem_fin, Vector.getElem_ofFn]
  rw [hopen]
  exact treeRecover_treeOpen _

end EthLib.Cryptography.Sphincs
