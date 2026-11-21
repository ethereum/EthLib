module

public import EthLib.Cryptography.Xmss.Tree
public import EthLib.Cryptography.Proofs.Xmss.Types
public import EthLib.Cryptography.Proofs.Merkle.Binding.SecondPreimage
public import EthLib.Cryptography.Proofs.Merkle.Build

/-!
# Proofs: the leanXMSS trees

An honest path leads from a key's leaf to the root of its tree.

On the bottom layer, key `idx` reaches the root of bottom tree `floor(idx / 2^16)`.

On the top layer, key `b < 2^16` reaches the root of the one top tree.

Another path that reaches the same root exposes a second preimage of `Th`, under one node address.

The tree hashes only at levels 1 to 16, so no node address holds a level reduced modulo 17.

Each statement specializes one proved for every Merkle tree.

A build of bottom tree `b` holds its root and the path of each of its keys.

The unfolding equations hold in every monad.

The other statements hold for every hash function `f`, run in the identity monad.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-! ## Unfolding, in any monad -/

section Monad

variable {m : Type → Type} [Monad m] (H : Array UInt64 → m Lanes4)
  (pp : PublicParam) (prf : SeedPrf m) (layer : Layer)

/-- A node on level 0 is the leaf of one-time key `j`. -/
theorem node_zero (j : Nat) :
    node H pp prf layer 0 j = otsPublicLeaf H pp prf layer (UInt32.ofNat j) :=
  rfl

/-- A node above level 0 hashes its two children, the left subtree first. -/
theorem node_succ (l j : Nat) :
    node H pp prf layer (l + 1) j = (do
      let left ← node H pp prf layer l (2 * j)
      let right ← node H pp prf layer l (2 * j + 1)
      nodeHash H pp layer ⟨l + 1, j⟩ left right) :=
  rfl

/-- The path of key `e` computes its siblings one level at a time, level 0 first.

The sibling on `level` is node `floor(e / 2^level) xor 1`. -/
theorem path_eq_ofFnInOrder [LawfulMonad m] (e : Nat) :
    path H pp prf layer e
      = ofFnInOrder LAYER_HEIGHT fun level =>
          node H pp prf layer level ((e / 2 ^ level.val) ^^^ 1) := by
  -- From any level, the siblings are the nodes above it in order.
  have siblings_eq : ∀ (n level j : Nat),
      Merkle.siblings (nodeHash H pp layer) (leaves H pp prf layer) ⟨level, j⟩ n
        = ofFnInOrder n fun i => node H pp prf layer (level + i.val) ((j / 2 ^ i.val) ^^^ 1) := by
    intro n
    induction n with
    | zero => intro level j; rfl
    | succ n ih =>
      intro level j
      simp only [Merkle.siblings, HashSig.ofFnInOrder_succ, Merkle.Position.parent_mk, ih]
      -- Entry `i + 1` is entry `i` one level up, with the index halved once more.
      have shift :
          (fun i : Fin n => node H pp prf layer (level + 1 + i.val) ((j / 2 / 2 ^ i.val) ^^^ 1))
            = fun i : Fin n =>
              node H pp prf layer (level + i.succ.val) ((j / 2 ^ i.succ.val) ^^^ 1) := by
        funext i
        rw [Fin.val_succ, Merkle.div_two_div_pow, Nat.add_assoc, Nat.add_comm 1 i.val]
      simp only [shift, Fin.val_zero, Nat.add_zero, Nat.pow_zero, Nat.div_one]
      rfl
  simpa [path, Merkle.path] using siblings_eq LAYER_HEIGHT 0 e

/-! ## Every level is read exactly

The node hash reads its level into the address modulo 17.

The tree hashes only at levels 1 to 16, where that read is exact.

So the address of every node of the tree names its true level. -/

/-- On levels up to 16, the node hash reads its level exactly into the address. -/
theorem nodeHash_of_le {p : Merkle.Position} (hlevel : p.level ≤ LAYER_HEIGHT)
    (left right : Digest) :
    nodeHash H pp layer p left right
      = th H pp (addrNode layer ⟨p.level, by omega⟩ (UInt32.ofNat p.index))
          #[left.lo, left.hi, right.lo, right.hi] := by
  simp only [nodeHash, Fin.ofNat, Nat.mod_eq_of_lt (Nat.lt_succ_of_le hlevel)]

/-- A node up to level 16 is the same with any node hash that agrees on levels 1 to 16. -/
theorem node_eq_of_agree (hash' : Merkle.Position → Digest → Digest → m Digest)
    (agree : ∀ q : Merkle.Position, 1 ≤ q.level → q.level ≤ LAYER_HEIGHT →
      nodeHash H pp layer q = hash' q)
    {level : Nat} (hlevel : level ≤ LAYER_HEIGHT) (j : Nat) :
    node H pp prf layer level j = Merkle.node hash' (leaves H pp prf layer) ⟨level, j⟩ :=
  Merkle.node_congr _ hash' _ ⟨level, j⟩ fun q h1 h2 => agree q h1 (by simp at h2; omega)

/-- A path is the same with any node hash that agrees on levels 1 to 16. -/
theorem path_eq_of_agree (hash' : Merkle.Position → Digest → Digest → m Digest)
    (agree : ∀ q : Merkle.Position, 1 ≤ q.level → q.level ≤ LAYER_HEIGHT →
      nodeHash H pp layer q = hash' q) (e : Nat) :
    path H pp prf layer e = Merkle.path hash' (leaves H pp prf layer) LAYER_HEIGHT e :=
  Merkle.path_congr _ hash' _ _ e fun q h1 h2 => agree q h1 (by omega)

/-- A fold is the same with any node hash that agrees on levels 1 to 16. -/
theorem fold_eq_of_agree (hash' : Merkle.Position → Digest → Digest → m Digest)
    (agree : ∀ q : Merkle.Position, 1 ≤ q.level → q.level ≤ LAYER_HEIGHT →
      nodeHash H pp layer q = hash' q) (e : Nat) (leaf : Digest)
    (pi : Vector Digest LAYER_HEIGHT) :
    fold H pp layer e leaf pi = Merkle.climb hash' ⟨0, e⟩ leaf pi.toList :=
  Merkle.climb_congr _ hash' _ ⟨0, e⟩ leaf fun q h1 h2 =>
    agree q (by omega) (by simpa using h2)

end Monad

/-! ## A build holds the root and the paths -/

section Build

variable {H : Array UInt64 → Id Lanes4} {pp : PublicParam} {prf : SeedPrf Id}
  {layer : Layer}

/-- The top value of a build is the node it is built at. -/
theorem value_build_run (level j : Nat) :
    (build H pp prf layer level j).run.value = (node H pp prf layer level j).run :=
  Merkle.value_build_run _ _ _

/-- The path of key `e`, read from the build of its tree, is the key's path. -/
theorem path_build_run (e : Nat) :
    (build H pp prf layer LAYER_HEIGHT (e / 2 ^ LAYER_HEIGHT)).run.path LAYER_HEIGHT e =
      (path H pp prf layer e).run :=
  Merkle.path_build_run _ _ _ _

end Build

/-! ## The path reaches the root -/

variable {f : Array UInt64 → Lanes4} {pp : PublicParam} {prf : SeedPrf Id} {layer : Layer}

/-- An honest path leads from key `e`'s leaf to node `floor(e / 2^16)` on the top level. -/
theorem fold_path (e : Nat) :
    (fold (pureHash f) pp layer e (node (pureHash f) pp prf layer 0 e).run
        (path (pureHash f) pp prf layer e).run).run
      = (node (pureHash f) pp prf layer LAYER_HEIGHT (e >>> LAYER_HEIGHT)).run := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Merkle.climb_path _ _ _ _

/-- On the top layer, key `b < 2^16` reaches the root of the one top tree. -/
theorem fold_path_top {b : Nat} (hb : b < 2 ^ LAYER_HEIGHT) :
    (fold (pureHash f) pp .top b (node (pureHash f) pp prf .top 0 b).run
        (path (pureHash f) pp prf .top b).run).run
      = (node (pureHash f) pp prf .top LAYER_HEIGHT 0).run :=
  Merkle.climb_path_root _ _ hb

/-! ## A path binds its leaf -/

/-- A path from key `e`'s leaf that reaches the root of its tree is honest.

That root is node `floor(e / 2^16)` on the top level: bottom tree `b`'s, or the top tree's.

Otherwise the search returns a second preimage of `Th`.

The preimage is under the address of an ancestor of the leaf:

- One input is that ancestor's two honest children.
- The other input is a different pair with the same hash.
-/
theorem fold_binding {e : Nat} {leaf : Digest} {pi : Vector Digest LAYER_HEIGHT}
    (heq : (fold (pureHash f) pp layer e leaf pi).run
      = (node (pureHash f) pp prf layer LAYER_HEIGHT (e >>> LAYER_HEIGHT)).run) :
    (leaf = (node (pureHash f) pp prf layer 0 e).run ∧
        pi = (path (pureHash f) pp prf layer e).run) ∨
      ∃ w, Merkle.findSecondPreimage (nodeHash (pureHash f) pp layer)
          (leaves (pureHash f) pp prf layer) ⟨0, e⟩ leaf pi.toList = some w ∧
        w.Valid (nodeHash (pureHash f) pp layer) (leaves (pureHash f) pp prf layer) ∧
        w.position.IsAncestor ⟨0, e⟩ ∧ 1 ≤ w.position.level ∧
          w.position.level ≤ LAYER_HEIGHT := by
  rw [Nat.shiftRight_eq_div_pow] at heq
  rcases Merkle.climb_binding_node (nodeHash (pureHash f) pp layer)
      (leaves (pureHash f) pp prf layer)
      LAYER_HEIGHT ⟨0, e⟩ leaf pi.toList (by simp) heq with ⟨hleaf, hpi⟩ | hfound
  · -- The siblings are the honest path, as lists and so as vectors.
    exact .inl ⟨hleaf, Vector.toList_inj.mp hpi⟩
  · -- The search returns a valid second preimage, on one of the 16 levels above the leaf.
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hfound
    obtain ⟨hvalid, hancestor, hlevel⟩ := Merkle.findSecondPreimage_valid _ _ _ _ _ w hw
    have hbelow := hancestor.level_le
    simp only [Merkle.Position.parent_level] at hbelow hlevel
    exact .inr ⟨w, hw, hvalid, hancestor.trans ⟨1, (Merkle.Position.ancestor_one _).symm⟩,
      by omega, by simpa using hlevel⟩

end EthLib.Cryptography.Xmss
