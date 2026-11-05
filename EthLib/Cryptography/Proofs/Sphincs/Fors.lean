module

public import EthLib.Cryptography.Sphincs.Fors
public import EthLib.Cryptography.Proofs.Sphincs.Tree
public import EthLib.Cryptography.Proofs.Xmss.Types

/-!
# Proofs: FORS

An honest FORS opening leads back to the instance's FORS key.

- Climbing levels 0 to 8 from leaf `l` reaches `Y_{9, floor(l / 512)}`.
- The last path node is the other one, `Y_{9, floor(l / 512) xor 1}`.
- Bit 9 of `l` puts the two in order, which gives `(Y_{9,0}, Y_{9,1})`.

Each step specializes a statement proved for every Merkle tree.

A FORS tree hashes only at levels 1 to 9, so its node addresses hold the true level and index.

The unfolding equations hold in every monad.

The other statements hold for every hash function `f`, run in the identity monad.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-- A leaf index is its own position. -/
theorem forsIndex_val (l : Fin (2 ^ FORS_HEIGHT)) : forsIndex l.val = l :=
  Fin.ext (Nat.mod_eq_of_lt l.isLt)

/-! ## Unfolding, in any monad -/

section Monad

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))
  {pp : PublicParam} {seed : Seed} {idx : Nat} {kappa : Fin FORS_TREES}

/-- Every FORS node above level 0 hashes its two children, the left subtree first. -/
theorem forsNode_succ (l j : Nat) :
    forsNode H pp seed idx kappa (l + 1) j = (do
      let left ← forsNode H pp seed idx kappa l (2 * j)
      let right ← forsNode H pp seed idx kappa l (2 * j + 1)
      forsNodeHash H pp idx kappa (l + 1) j left right) :=
  rfl

/-- On levels up to 15 and indices below `2^10`, the node hash reads its position exactly. -/
theorem forsNodeHash_of_lt {level j : Nat} (hlevel : level < 16) (hj : j < 2 ^ FORS_HEIGHT)
    (left right : Digest) :
    forsNodeHash H pp idx kappa level j left right
      = th H pp (addrForsNode idx kappa ⟨level, hlevel⟩ ⟨j, hj⟩)
          (packBytes left ++ packBytes right) := by
  simp only [forsNodeHash, Fin.ofNat, forsIndex, Nat.mod_eq_of_lt hlevel, Nat.mod_eq_of_lt hj]

/-- A node up to level 9 is the same with any node hash that agrees on levels 1 to 9. -/
theorem forsNode_eq_of_agree (hash' : Nat → Nat → Digest → Digest → m Digest)
    (agree : ∀ k, 1 ≤ k → k < FORS_HEIGHT → forsNodeHash H pp idx kappa k = hash' k)
    {level : Nat} (hlevel : level < FORS_HEIGHT) (j : Nat) :
    forsNode H pp seed idx kappa level j
      = Merkle.node hash' (forsLeaves H pp seed idx kappa) level j :=
  Merkle.node_congr _ hash' _ level j fun k h1 h2 => agree k h1 (by omega)

/-- The leaf an opening reveals hashes to the honest level-0 node. -/
theorem forsLeafHash_forsSecret (l : Fin (2 ^ FORS_HEIGHT)) :
    (forsSecret H pp seed idx kappa l >>= forsLeafHash H pp idx kappa l)
      = forsNode H pp seed idx kappa 0 l.val := by
  simp only [forsNode, Merkle.node, forsLeaves, forsIndex_val]

end Monad

/-! ## An honest opening leads to the FORS key -/

variable {f : ByteArray → Vector UInt8 32} {pp : PublicParam} {seed : Seed} {idx : Nat}
  {kappa : Fin FORS_TREES}

/-- What an opening computes: the leaf's secret and the leaf's path. -/
theorem treeOpen_run (l : Fin (2 ^ FORS_HEIGHT)) :
    (treeOpen (pureHash f) pp seed idx kappa l).run
      = { secret := (forsSecret (pureHash f) pp seed idx kappa l).run
          path := (Merkle.path (forsNodeHash (pureHash f) pp idx kappa)
            (forsLeaves (pureHash f) pp seed idx kappa) FORS_HEIGHT l).run } :=
  rfl

/-- An opening's path is the same with any node hash that agrees on levels 1 to 9. -/
theorem treeOpen_path_eq_of_agree (hash' : Nat → Nat → Digest → Digest → Id Digest)
    (agree : ∀ k, 1 ≤ k → k < FORS_HEIGHT → forsNodeHash (pureHash f) pp idx kappa k = hash' k)
    (l : Fin (2 ^ FORS_HEIGHT)) :
    (treeOpen (pureHash f) pp seed idx kappa l).run.path
      = (Merkle.path hash' (forsLeaves (pureHash f) pp seed idx kappa) FORS_HEIGHT l).run := by
  rw [treeOpen_run, Merkle.path_congr _ hash' _ _ _ agree]

/-- An honest opening of one tree recovers the tree's two level-9 nodes, in order. -/
theorem treeRecover_treeOpen (l : Fin (2 ^ FORS_HEIGHT)) :
    (treeRecover (pureHash f) pp idx kappa l (treeOpen (pureHash f) pp seed idx kappa l).run).run
      = ((forsNode (pureHash f) pp seed idx kappa (FORS_HEIGHT - 1) 0).run,
          (forsNode (pureHash f) pp seed idx kappa (FORS_HEIGHT - 1) 1).run) := by
  -- The leaf hashed from the revealed secret is the honest level-0 node.
  have hleaf : (forsLeafHash (pureHash f) pp idx kappa l
      (forsSecret (pureHash f) pp seed idx kappa l).run).run
        = (forsLeaves (pureHash f) pp seed idx kappa l.val).run :=
    congrArg Id.run (forsLeafHash_forsSecret (pureHash f) l)
  simp only [treeRecover, treeOpen_run, Id.run_bind, Id.run_pure, hleaf]
  -- Bit 9 of `l` is the low bit of `floor(l / 2^9)`.
  rw [Nat.shiftRight_eq_div_pow]
  -- The climb reaches one level-9 node, and the last path node is the other one, in order.
  rw [Merkle.ordered_climb_path_last _ _ (by decide)]
  -- A leaf below `2^10` has a level-9 ancestor of index 0 or 1, so their parent is node 0.
  have hl : l.val < 1024 := l.isLt
  have hparent : l.val / 2 ^ (FORS_HEIGHT - 1) / 2 = 0 := by
    show l.val / 512 / 2 = 0
    omega
  rw [hparent, Nat.mul_zero, Nat.zero_add]
  rfl

/-- Honest openings of every tree recover the instance's FORS key. -/
theorem forsRecover_forsSign (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES) :
    (forsRecover (pureHash f) pp idx leaves (forsSign (pureHash f) pp seed idx leaves).run).run
      = (forsKey (pureHash f) pp seed idx).run := by
  -- Tree by tree, the opening recovers the tree's part of the key.
  have hsign : (forsSign (pureHash f) pp seed idx leaves).run
      = Vector.ofFn fun kappa => (treeOpen (pureHash f) pp seed idx kappa leaves[kappa]).run :=
    Xmss.ofFnInOrder_run _ _
  rw [hsign, forsRecover, Xmss.ofFnInOrder_run, forsKey, Xmss.ofFnInOrder_run]
  refine congrArg Vector.ofFn (funext fun kappa => ?_)
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  exact treeRecover_treeOpen _

end EthLib.Cryptography.Sphincs
