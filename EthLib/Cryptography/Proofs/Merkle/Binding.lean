import EthLib.Cryptography.Proofs.Merkle.Tree

/-!
# Proofs: a path binds its leaf

Two climbs from one position that meet are equal, or the node hash collides.

The collision has a known position: an ancestor of the starting node.

So a hash tweaked by its position collides under one tweak.

Against an honest tree the statement is sharper.

A climb that reaches an honest node but is not the honest one gives a second preimage.

That is a pair other than the honest children of some ancestor, with the same hash.
-/

namespace EthLib.Cryptography.Merkle

variable {α : Type} (hash : Nat → Nat → α → α → α)

/-- Two different pairs of children that hash to one parent at position `(level, j)`. -/
def Collision (level j : Nat) : Prop :=
  ∃ x y : α × α, x ≠ y ∧ hash level j x.1 x.2 = hash level j y.1 y.2

/-- A pair other than the honest children of node `(level + 1, j)` that hashes to that node. -/
def SecondPreimage (leaves : Nat → α) (level j : Nat) : Prop :=
  ∃ y : α × α, y ≠ (node hash leaves level (2 * j), node hash leaves level (2 * j + 1)) ∧
    hash (level + 1) j y.1 y.2 = node hash leaves (level + 1) j

/-! ## Any two climbs -/

/-- Two climbs from `(level, j)` over equally many siblings that meet are equal, or the hash collides.

The collision is at an ancestor: `k + 1` levels up, at index `j / 2^(k + 1)`. -/
theorem climb_binding :
    ∀ (p q : List α) (level j : Nat) (a b : α), p.length = q.length →
      climb hash level j a p = climb hash level j b q →
      (a = b ∧ p = q) ∨ ∃ k < p.length, Collision hash (level + k + 1) (j / 2 ^ (k + 1)) := by
  intro p
  induction p with
  | nil =>
    intro q level j a b hl heq
    cases q with
    | nil => exact .inl ⟨heq, rfl⟩
    | cons _ _ => simp at hl
  | cons s rest ih =>
    intro q level j a b hl heq
    cases q with
    | nil => simp at hl
    | cons t rest' =>
      rw [climb_cons, climb_cons] at heq
      rcases ih rest' (level + 1) (j / 2) _ _ (by simpa using hl) heq with ⟨hparent, hrest⟩ | ⟨k, hk, hcol⟩
      · by_cases hpair : ordered j a s = ordered j b t
        · -- Equal pairs: the held nodes and the first siblings agree.
          obtain ⟨rfl, rfl⟩ := ordered_inj.mp hpair
          exact .inl ⟨rfl, by rw [hrest]⟩
        · -- Different pairs with one parent: a collision one level up.
          exact .inr ⟨0, by simp, _, _, hpair, by simpa using hparent⟩
      · -- A collision further up stays a collision, one level higher in the count.
        refine .inr ⟨k + 1, by simpa using hk, ?_⟩
        rwa [div_two_div_pow, show level + 1 + k + 1 = level + (k + 1) + 1 by omega] at hcol

/-! ## Against an honest tree -/

/-- A climb from `(level, j)` over `n` siblings that reaches the honest ancestor is honest, or gives a second preimage.

The second preimage is of the ancestor `k + 1` levels up, at index `j / 2^(k + 1)`. -/
theorem climb_binding_node (leaves : Nat → α) :
    ∀ (n level j : Nat) (b : α) (q : List α), q.length = n →
      climb hash level j b q = node hash leaves (level + n) (j / 2 ^ n) →
      (b = node hash leaves level j ∧ q = siblings hash leaves level j n) ∨
        ∃ k < n, SecondPreimage hash leaves (level + k) (j / 2 ^ (k + 1)) := by
  intro n
  induction n with
  | zero =>
    intro level j b q hl heq
    -- No sibling: the climb is its start, which must be the honest node.
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    exact .inl ⟨by simpa using heq, rfl⟩
  | succ n ih =>
    intro level j b q hl heq
    cases q with
    | nil => simp at hl
    | cons t rest =>
      rw [climb_cons, ← div_two_div_pow, show level + (n + 1) = level + 1 + n by omega] at heq
      rcases ih (level + 1) (j / 2) _ rest (by simpa using hl) heq with ⟨hparent, hrest⟩ | ⟨k, hk, hsp⟩
      · -- The honest children, in order, are the honest node and its sibling.
        have honest := ordered_sibling (node hash leaves level) j
        by_cases hpair : ordered j b t = ordered j (node hash leaves level j) (node hash leaves level (j ^^^ 1))
        · obtain ⟨rfl, rfl⟩ := ordered_inj.mp hpair
          exact .inl ⟨rfl, by rw [siblings, hrest]⟩
        · -- Another pair with the honest parent's hash: a second preimage one level up.
          refine .inr ⟨0, by simp, ordered j b t, ?_, ?_⟩
          · simp only [Nat.add_zero, Nat.zero_add, Nat.pow_one]
            rwa [← honest]
          simpa [node_succ] using hparent
      · -- A second preimage further up stays one, one level higher in the count.
        refine .inr ⟨k + 1, by simpa using hk, ?_⟩
        rwa [div_two_div_pow, show level + 1 + k = level + (k + 1) by omega] at hsp

end EthLib.Cryptography.Merkle
