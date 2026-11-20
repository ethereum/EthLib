module

public import EthLib.Cryptography.Proofs.Merkle.Completeness

/-!
# Proofs: a built tree holds the nodes and the paths

A build is the node at its position, computed with a hash that keeps each node's two subtrees.

So every fact about nodes applies to it: its calls, their order, and maps of monads.

In every lawful monad, the top value of a build is the node at its position.

In the identity monad, the path read from a build is the path of the tree, sibling for sibling.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle

/-! ## Unfolding, in any monad -/

section Monad

variable {m : Type → Type} [Monad m] {α : Type} (hash : Position → α → α → m α)

/-- A build on level 0 is a leaf. -/
theorem build_zero (leaves : Nat → m α) (j : Nat) :
    build hash leaves ⟨0, j⟩ = (do
      let value ← leaves j
      return .leaf value) :=
  rfl

/-- A build above level 0 builds its two children, the left one first, then hashes their values. -/
theorem build_succ (leaves : Nat → m α) (level j : Nat) :
    build hash leaves ⟨level + 1, j⟩ = (do
      let left ← build hash leaves ⟨level, 2 * j⟩
      let right ← build hash leaves ⟨level, 2 * j + 1⟩
      let value ← hash ⟨level + 1, j⟩ left.value right.value
      return .node value left right) :=
  rfl

/-- The top value of a build is the node at its position. -/
theorem value_build [LawfulMonad m] (leaves : Nat → m α) :
    ∀ p : Position, Built.value <$> build hash leaves p = node hash leaves p := by
  rintro ⟨level, j⟩
  induction level generalizing j with
  | zero => simp [build_zero, node_zero, Built.value]
  | succ level ih =>
    -- Each child's build gives its node, and the hash reads only the two values.
    rw [build_succ, node_succ, ← ih, ← ih]
    simp [Built.value]

/-- A property kept by `pure` and `bind`, and true of the leaves and the hash, holds of a build. -/
theorem build_rec (P : ∀ {β : Type}, m β → Prop) (hpure : ∀ {β : Type} (b : β), P (pure b))
    (hbind : ∀ {β γ : Type} {x : m β} {f : β → m γ}, P x → (∀ b, P (f b)) → P (x >>= f))
    (leaves : Nat → m α) (hleaves : ∀ j, P (leaves j))
    (hhash : ∀ p left right, P (hash p left right)) :
    ∀ p : Position, P (build hash leaves p) :=
  node_rec _ P hbind _ (fun j => hbind (hleaves j) fun _ => hpure _)
    (fun _ _ _ => hbind (hhash _ _ _) fun _ => hpure _)

/-- A map of monads that keeps `pure` and `bind` sends a build to the build of the mapped hash. -/
theorem build_map {n : Type → Type} [Monad n] (φ : ∀ {β : Type}, m β → n β)
    (map_pure : ∀ {β : Type} (b : β), φ (pure b) = pure b)
    (map_bind : ∀ {β γ : Type} (x : m β) (f : β → m γ), φ (x >>= f) = φ x >>= fun b => φ (f b))
    (leaves : Nat → m α) (p : Position) :
    φ (build hash leaves p) =
      build (fun p left right => φ (hash p left right)) (fun j => φ (leaves j)) p := by
  simp only [build, node_map _ φ map_bind, map_bind, map_pure]

end Monad

/-! ## The nodes and the paths, in the identity monad -/

section Run

variable {α : Type} (hash : Position → α → α → Id α)

/-- The top value of a build is the node at its position. -/
theorem value_build_run (leaves : Nat → Id α) (p : Position) :
    (build hash leaves p).run.value = (node hash leaves p).run := by
  rw [← value_build]
  rfl

/-- Sibling `i` of the siblings above a position is the sibling of its ancestor `i` levels up. -/
theorem getElem_siblings_run (leaves : Nat → Id α) :
    ∀ (n : Nat) (p : Position) (i : Nat) (hi : i < n),
      (siblings hash leaves p n).run[i] =
        (node hash leaves ⟨p.level + i, (p.index / 2 ^ i) ^^^ 1⟩).run
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, p, i, hi => by
    simp only [siblings, Id.run_bind, Id.run_pure, Vector.getElem_cast]
    cases i with
    | zero => simp [Position.sibling]
    | succ i =>
      -- Entry `i + 1` is entry `i` of the siblings one level up.
      simp only [Vector.getElem_append, dite_eq_right (show ¬i + 1 < 1 by omega),
        Nat.add_sub_cancel, getElem_siblings_run leaves n p.parent i (by omega),
        Position.parent_level, Position.parent_index, div_two_div_pow,
        Nat.add_right_comm p.level 1 i, Nat.add_assoc p.level i 1]

/-- Sibling `i` read from a build `n` levels above leaf `j` is on level `i`.

Its index is `floor(j / 2^i) xor 1`. -/
theorem getElem_path_build_run (leaves : Nat → Id α) :
    ∀ (n j i : Nat) (hi : i < n),
      ((build hash leaves ⟨n, j / 2 ^ n⟩).run.path n j)[i] =
        (node hash leaves ⟨i, (j / 2 ^ i) ^^^ 1⟩).run
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, j, i, hi => by
    -- The child on the leaf's side is node `floor(j / 2^n)`, and the other child is its sibling.
    have hhalf : j / 2 ^ n / 2 = j / 2 ^ (n + 1) := div_pow_div_two j n
    have hbuild : (build hash leaves ⟨n + 1, j / 2 ^ (n + 1)⟩).run = .node
        (hash ⟨n + 1, j / 2 ^ (n + 1)⟩ (build hash leaves ⟨n, 2 * (j / 2 ^ (n + 1))⟩).run.value
          (build hash leaves ⟨n, 2 * (j / 2 ^ (n + 1)) + 1⟩).run.value).run
        (build hash leaves ⟨n, 2 * (j / 2 ^ (n + 1))⟩).run
        (build hash leaves ⟨n, 2 * (j / 2 ^ (n + 1)) + 1⟩).run := rfl
    have hpath : (build hash leaves ⟨n + 1, j / 2 ^ (n + 1)⟩).run.path (n + 1) j =
        ((build hash leaves ⟨n, j / 2 ^ n⟩).run.path n j).push
          (node hash leaves ⟨n, (j / 2 ^ n) ^^^ 1⟩).run := by
      rw [hbuild, Built.path]
      by_cases hbit : j / 2 ^ n % 2 = 0
      · have hchild : 2 * (j / 2 ^ (n + 1)) = j / 2 ^ n := by omega
        rw [ite_eq_left hbit, hchild, value_build_run, xor_one_of_even hbit]
      · have hchild : 2 * (j / 2 ^ (n + 1)) + 1 = j / 2 ^ n := by omega
        rw [ite_eq_right hbit, hchild, value_build_run, xor_one_of_odd (by omega), ← hchild,
          Nat.add_sub_cancel]
    rw [hpath, Vector.getElem_push]
    split
    · exact getElem_path_build_run leaves n j i (by omega)
    · rw [show i = n by omega]

/-- The path read from a build `h` levels above leaf `j` is the path of leaf `j`. -/
theorem path_build_run (leaves : Nat → Id α) (h j : Nat) :
    (build hash leaves ⟨h, j / 2 ^ h⟩).run.path h j = (path hash leaves h j).run := by
  ext i hi
  rw [getElem_path_build_run hash leaves h j i hi, path, getElem_siblings_run hash leaves h _ i hi]
  simp

end Run

end EthLib.Cryptography.Merkle
