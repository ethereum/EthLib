module

public import EthLib.Cryptography.Xmss.Tree
public import EthLib.Cryptography.Proofs.Xmss.Types
public import EthLib.Cryptography.Proofs.Merkle.Binding

/-!
# Proofs: `Xmss.Tree`

An honest path leads from a key's leaf to the root of its tree.

On the bottom layer, key `idx` reaches the root of bottom tree `floor(idx / 2^16)`.

On the top layer, key `b < 2^16` reaches the root of the one top tree.

Another path that reaches the same root exposes a second preimage of `Th`, under one node address.

Each statement specializes one proved for every Merkle tree.

The unfolding equations hold in every monad.

The other statements hold for every hash function `f`, run in the identity monad.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-! ## Unfolding, in any monad -/

section Monad

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))
  (pp : PublicParam) (seed : Seed) (layer : Layer)

/-- A node on level 0 is the leaf of one-time key `j`. -/
theorem node_zero (j : Nat) :
    node H pp seed layer 0 j = otsPublicLeaf H pp seed layer (UInt32.ofNat j) :=
  rfl

/-- A node above level 0 hashes its two children, the left subtree first. -/
theorem node_succ (l j : Nat) :
    node H pp seed layer (l + 1) j = (do
      let left ← node H pp seed layer l (2 * j)
      let right ← node H pp seed layer l (2 * j + 1)
      nodeHash H pp layer (l + 1) j left right) :=
  rfl

/-- The path of key `e` computes its siblings one level at a time, level 0 first.

The sibling on `level` is node `floor(e / 2^level) xor 1`. -/
theorem path_eq_ofFnInOrder [LawfulMonad m] (e : Nat) :
    path H pp seed layer e
      = ofFnInOrder LAYER_HEIGHT fun level =>
          node H pp seed layer level ((e / 2 ^ level.val) ^^^ 1) := by
  -- From any level, the siblings are the nodes above it in order.
  have siblings_eq : ∀ (n level j : Nat),
      Merkle.siblings (nodeHash H pp layer) (leaves H pp seed layer) level j n
        = ofFnInOrder n fun i => node H pp seed layer (level + i.val) ((j / 2 ^ i.val) ^^^ 1) := by
    intro n
    induction n with
    | zero => intro level j; rfl
    | succ n ih =>
      intro level j
      simp only [Merkle.siblings, ofFnInOrder, ih]
      -- Entry `i + 1` is entry `i` one level up, with the index halved once more.
      have shift :
          (fun i : Fin n => node H pp seed layer (level + 1 + i.val) ((j / 2 / 2 ^ i.val) ^^^ 1))
            = fun i : Fin n =>
              node H pp seed layer (level + i.succ.val) ((j / 2 ^ i.succ.val) ^^^ 1) := by
        funext i
        rw [Fin.val_succ, Merkle.div_two_div_pow, Nat.add_assoc, Nat.add_comm 1 i.val]
      simp only [shift, Fin.val_zero, Nat.add_zero, Nat.pow_zero, Nat.div_one]
      rfl
  simpa [path, Merkle.path] using siblings_eq LAYER_HEIGHT 0 e

end Monad

/-! ## The path reaches the root -/

variable {f : ByteArray → Vector UInt8 32} {pp : PublicParam} {seed : Seed} {layer : Layer}

/-- An honest path leads from key `e`'s leaf to node `floor(e / 2^16)` on the top level. -/
theorem fold_path (e : Nat) :
    (fold (pureHash f) pp layer e (node (pureHash f) pp seed layer 0 e).run
        (path (pureHash f) pp seed layer e).run).run
      = (node (pureHash f) pp seed layer LAYER_HEIGHT (e >>> LAYER_HEIGHT)).run := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Merkle.climb_path _ _ _ _

/-- On the top layer, key `b < 2^16` reaches the root of the one top tree. -/
theorem fold_path_top {b : Nat} (hb : b < 2 ^ LAYER_HEIGHT) :
    (fold (pureHash f) pp .top b (node (pureHash f) pp seed .top 0 b).run
        (path (pureHash f) pp seed .top b).run).run
      = (node (pureHash f) pp seed .top LAYER_HEIGHT 0).run :=
  Merkle.climb_path_root _ _ hb

/-! ## A path binds its leaf -/

/-- A path from key `e`'s leaf that reaches the root of its tree is honest.

That root is node `floor(e / 2^16)` on the top level: bottom tree `b`'s, or the top tree's.

Otherwise some level holds a second preimage of `Th` under the address of an ancestor of the leaf:

- one input is that ancestor's two honest children;
- the other is a different pair with the same hash.
-/
theorem fold_binding {e : Nat} {leaf : Digest} {pi : Vector Digest LAYER_HEIGHT}
    (heq : (fold (pureHash f) pp layer e leaf pi).run
      = (node (pureHash f) pp seed layer LAYER_HEIGHT (e >>> LAYER_HEIGHT)).run) :
    (leaf = (node (pureHash f) pp seed layer 0 e).run ∧
        pi = (path (pureHash f) pp seed layer e).run) ∨
      ∃ k < LAYER_HEIGHT,
        Merkle.SecondPreimage (nodeHash (pureHash f) pp layer) (leaves (pureHash f) pp seed layer) k
          (e / 2 ^ (k + 1)) := by
  rw [Nat.shiftRight_eq_div_pow] at heq
  rcases Merkle.climb_binding_node (nodeHash (pureHash f) pp layer)
      (leaves (pureHash f) pp seed layer)
      LAYER_HEIGHT 0 e leaf pi.toList (by simp) heq with ⟨hleaf, hpi⟩ | ⟨k, hk, hsp⟩
  · -- The siblings are the honest path, as lists and so as vectors.
    exact .inl ⟨hleaf, Vector.toList_inj.mp hpi⟩
  · exact .inr ⟨k, hk, by simpa using hsp⟩

end EthLib.Cryptography.Xmss
