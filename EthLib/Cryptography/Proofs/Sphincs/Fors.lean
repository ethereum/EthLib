module

public import EthLib.Cryptography.Sphincs.Fors
public import EthLib.Cryptography.Proofs.Sphincs.Tree
public import EthLib.Cryptography.Proofs.HashSig

/-!
# Proofs: FORS

An honest FORS opening leads back to the instance's FORS public key.

- Climbing all 10 heights from leaf `s` with its path reaches the tree's root `Y_{10,0}`.
- The 24 roots, hashed by `T_k`, are the FORS public key.

Each step specializes a statement proved for every Merkle tree.

A FORS tree hashes only at heights 1 to 10, so only those node hashes matter.

The unfolding equations hold in every monad.

The other statements hold for every hash function `f`, run in the identity monad.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-! ## Unfolding, in any monad -/

section Monad

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))
  {pkSeed : PkSeed} {prf : Prf m} {idx : Nat} {kappa : Fin FORS_TREES}

/-- Every FORS node above height 0 hashes its two children, the left subtree first. -/
theorem forsNode_succ (z j : Nat) :
    forsNode H pkSeed prf idx kappa (z + 1) j = (do
      let left ← forsNode H pkSeed prf idx kappa z (2 * j)
      let right ← forsNode H pkSeed prf idx kappa z (2 * j + 1)
      forsNodeHash H pkSeed idx kappa (z + 1) j left right) :=
  rfl

/-- A node at height `z` is the same with any node hash that agrees on heights 1 to `z`. -/
theorem forsNode_eq_of_agree (hash' : Nat → Nat → Digest → Digest → m Digest) {z : Nat}
    (agree : ∀ k, 1 ≤ k → k ≤ z → forsNodeHash H pkSeed idx kappa k = hash' k) (j : Nat) :
    forsNode H pkSeed prf idx kappa z j
      = Merkle.node hash' (forsLeaves H pkSeed prf idx kappa) z j :=
  Merkle.node_congr _ hash' _ z j agree

/-- A tree's root is the same with any node hash that agrees on heights 1 to 10. -/
theorem forsRoot_eq_of_agree (hash' : Nat → Nat → Digest → Digest → m Digest)
    (agree : ∀ k, 1 ≤ k → k ≤ FORS_HEIGHT → forsNodeHash H pkSeed idx kappa k = hash' k) :
    forsRoot H pkSeed prf idx kappa
      = Merkle.root hash' (forsLeaves H pkSeed prf idx kappa) FORS_HEIGHT :=
  Merkle.node_congr _ hash' _ _ 0 agree

/-- The leaf an opening reveals hashes to the honest node at height 0. -/
theorem forsLeafHash_forsSecret (s : Nat) :
    (forsSecret prf idx kappa s >>= forsLeafHash H pkSeed idx kappa s)
      = forsNode H pkSeed prf idx kappa 0 s :=
  rfl

/-- The tree's root is its one node at height 10. -/
theorem forsRoot_eq_forsNode :
    forsRoot H pkSeed prf idx kappa = forsNode H pkSeed prf idx kappa FORS_HEIGHT 0 :=
  rfl

end Monad

/-! ## The values computed -/

variable {f : ByteArray → Vector UInt8 32} {pkSeed : PkSeed} {prf : Prf Id} {idx : Nat}
  {kappa : Fin FORS_TREES}

/-- What an opening computes: the leaf's secret and the leaf's path. -/
theorem treeOpen_run (s : Fin (2 ^ FORS_HEIGHT)) :
    (treeOpen (pureHash f) pkSeed prf idx kappa s).run
      = { secret := (forsSecret prf idx kappa s.val).run
          path := (Merkle.path (forsNodeHash (pureHash f) pkSeed idx kappa)
            (forsLeaves (pureHash f) pkSeed prf idx kappa) FORS_HEIGHT s.val).run } :=
  rfl

/-- An opening's path is the same with any node hash that agrees on heights 1 to 9.

The path holds nodes below height 10, so the hash at height 10 plays no part. -/
theorem treeOpen_path_eq_of_agree (hash' : Nat → Nat → Digest → Digest → Id Digest)
    (agree : ∀ k, 1 ≤ k → k < FORS_HEIGHT →
      forsNodeHash (pureHash f) pkSeed idx kappa k = hash' k)
    (s : Fin (2 ^ FORS_HEIGHT)) :
    (treeOpen (pureHash f) pkSeed prf idx kappa s).run.path
      = (Merkle.path hash' (forsLeaves (pureHash f) pkSeed prf idx kappa) FORS_HEIGHT s).run := by
  rw [treeOpen_run, Merkle.path_congr _ hash' _ _ _ agree]

/-- What the FORS public key computes: `T_k` over the 24 roots, tree 0 first. -/
theorem forsKey_run :
    (forsKey (pureHash f) pkSeed prf idx).run
      = (forsPkFromRoots (pureHash f) pkSeed idx
          (Vector.ofFn fun kappa => (forsRoot (pureHash f) pkSeed prf idx kappa).run)).run := by
  rw [forsKey, Id.run_bind, HashSig.ofFnInOrder_run]

/-- What recovering the FORS public key computes: `T_k` over the 24 recovered roots. -/
theorem forsRecover_run (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES)
    (openings : Vector TreeOpening FORS_TREES) :
    (forsRecover (pureHash f) pkSeed idx leaves openings).run
      = (forsPkFromRoots (pureHash f) pkSeed idx (Vector.ofFn fun kappa =>
          (treeRecover (pureHash f) pkSeed idx kappa leaves[kappa] openings[kappa]).run)).run := by
  rw [forsRecover, Id.run_bind, HashSig.ofFnInOrder_run]

/-! ## An honest opening leads to the FORS public key -/

/-- An honest opening of one tree recovers the tree's root. -/
theorem treeRecover_treeOpen (s : Fin (2 ^ FORS_HEIGHT)) :
    (treeRecover (pureHash f) pkSeed idx kappa s
        (treeOpen (pureHash f) pkSeed prf idx kappa s).run).run
      = (forsRoot (pureHash f) pkSeed prf idx kappa).run :=
  -- The revealed secret hashes to the honest leaf, and the honest path climbs to the root.
  Merkle.climb_path_root (forsNodeHash (pureHash f) pkSeed idx kappa)
    (forsLeaves (pureHash f) pkSeed prf idx kappa) s.isLt

/-- Honest openings of every tree recover the instance's FORS public key. -/
theorem forsRecover_forsSign (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES) :
    (forsRecover (pureHash f) pkSeed idx leaves
        (forsSign (pureHash f) pkSeed prf idx leaves).run).run
      = (forsKey (pureHash f) pkSeed prf idx).run := by
  -- Tree by tree, the opening recovers the tree's root.
  have hsign : (forsSign (pureHash f) pkSeed prf idx leaves).run
      = Vector.ofFn fun kappa => (treeOpen (pureHash f) pkSeed prf idx kappa leaves[kappa]).run :=
    HashSig.ofFnInOrder_run _ _
  rw [forsRecover_run, forsKey_run, hsign]
  refine congrArg (fun roots => (forsPkFromRoots (pureHash f) pkSeed idx roots).run)
    (congrArg Vector.ofFn (funext fun kappa => ?_))
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  exact treeRecover_treeOpen _

end EthLib.Cryptography.Sphincs
