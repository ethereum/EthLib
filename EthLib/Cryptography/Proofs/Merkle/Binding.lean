module

public import EthLib.Cryptography.Proofs.Merkle.Completeness

/-!
# Proofs: a path binds its leaf

A real node hash compresses two nodes into one, so collisions exist.

A statement "the climbs are equal, or a collision exists" would then say nothing.

So each theorem here names an algorithm that computes the collision from the two climbs.

That algorithm is the reduction: whoever forges a path also finds a collision.

Each search takes one step per level, and no theorem here counts its hash calls.

- `findCollision` walks two climbs from one position up, level by level.
- It returns the first level where they hash two different pairs to one parent.
- `findSecondPreimage` does the same for one climb against an honest tree.
- It returns the first level where the climb hashes another pair to the honest node.

The position found is an ancestor of the starting node.

So a hash tweaked by its position collides under one tweak.

The statements hold for every node hash, run in the identity monad.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle

variable {α : Type} (hash : Nat → Nat → α → α → Id α)

/-! ## Any two climbs -/

/-- Two pairs of children offered for the node at `(level, j)`. -/
structure Collision (α : Type) where
  /-- The level of the parent. -/
  level : Nat
  /-- The index of the parent on its level. -/
  j : Nat
  /-- The first pair, left child first. -/
  x : α × α
  /-- The second pair, left child first. -/
  y : α × α

/-- The two pairs differ, and hash to one parent at their position. -/
def Collision.Valid (c : Collision α) : Prop :=
  c.x ≠ c.y ∧ (hash c.level c.j c.x.1 c.x.2).run = (hash c.level c.j c.y.1 c.y.2).run

/-- The collision two climbs from `(level, j)` run into, at the lowest level where one exists.

On each level, both climbs hash their held node with their sibling, in the order the index gives.

A level where the two pairs differ but the parents agree is a collision. -/
def findCollision [DecidableEq α] : (level j : Nat) → (a b : α) → (p q : List α) → Option (Collision α)
  | level, j, a, b, s :: p, t :: q =>
    let x := ordered j a s
    let y := ordered j b t
    let parentA := (hash (level + 1) (j / 2) x.1 x.2).run
    let parentB := (hash (level + 1) (j / 2) y.1 y.2).run
    if x ≠ y ∧ parentA = parentB then some ⟨level + 1, j / 2, x, y⟩
    else findCollision (level + 1) (j / 2) parentA parentB p q
  | _, _, _, _, _, _ => none

/-- Every collision the search returns is valid, at an ancestor of `(level, j)`.

The ancestor is `k + 1` levels up, at index `j / 2^(k + 1)`.

Its two pairs are the ones the two climbs hash there, after `k` levels. -/
theorem findCollision_valid [DecidableEq α] :
    ∀ (p q : List α) (level j : Nat) (a b : α) (c : Collision α),
      findCollision hash level j a b p q = some c →
      c.Valid hash ∧ ∃ k s t, p[k]? = some s ∧ q[k]? = some t ∧
        c.level = level + k + 1 ∧ c.j = j / 2 ^ (k + 1) ∧
        c.x = ordered (j / 2 ^ k) (climb hash level j a (p.take k)).run s ∧
        c.y = ordered (j / 2 ^ k) (climb hash level j b (q.take k)).run t := by
  intro p
  induction p with
  | nil => intro q level j a b c h; simp [findCollision] at h
  | cons s rest ih =>
    intro q level j a b c h
    cases q with
    | nil => simp [findCollision] at h
    | cons t rest' =>
      simp only [findCollision] at h
      split at h
      · -- This level is the collision.
        rename_i hfound
        cases h
        exact ⟨hfound, 0, s, t, rfl, rfl, rfl, by simp, by simp, by simp⟩
      · -- The collision is further up: one level higher in the count.
        obtain ⟨hvalid, k, s', t', hs, ht, hlevel, hj, hx, hy⟩ :=
          ih rest' (level + 1) (j / 2) _ _ c h
        refine ⟨hvalid, k + 1, s', t', hs, ht, by omega, ?_, ?_, ?_⟩ <;>
          rw [div_two_div_pow] at * <;> assumption

/-- One climb compared with itself runs into no collision. -/
theorem findCollision_self [DecidableEq α] :
    ∀ (p : List α) (level j : Nat) (a : α), findCollision hash level j a a p p = none
  | [], _, _, _ => rfl
  | s :: rest, level, j, a => by
    -- The two pairs at each level are the same pair.
    simp only [findCollision, ne_eq, not_true_eq_false, false_and, ↓reduceIte,
      findCollision_self rest]

/-- Binding: two climbs from `(level, j)` over equally many siblings that meet are equal.

Otherwise `findCollision` finds a collision of the node hash, valid by `findCollision_valid`. -/
theorem climb_binding [DecidableEq α] :
    ∀ (p q : List α) (level j : Nat) (a b : α), p.length = q.length →
      (climb hash level j a p).run = (climb hash level j b q).run →
      (a = b ∧ p = q) ∨ (findCollision hash level j a b p q).isSome := by
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
      simp only [findCollision]
      -- When this level is a collision, the search stops here.
      by_cases hfound : ordered j a s ≠ ordered j b t ∧
          (hash (level + 1) (j / 2) (ordered j a s).1 (ordered j a s).2).run
            = (hash (level + 1) (j / 2) (ordered j b t).1 (ordered j b t).2).run
      · exact .inr (by simp [hfound])
      simp only [hfound, ↓reduceIte]
      rcases ih rest' (level + 1) (j / 2) _ _ (by simpa using hl) heq with
        ⟨hparent, hrest⟩ | hsome
      · -- Equal parents and no collision here: the pairs are equal, so the climbs are.
        have hpair : ordered j a s = ordered j b t :=
          Classical.byContradiction fun hne => hfound ⟨hne, hparent⟩
        obtain ⟨rfl, rfl⟩ := ordered_inj.mp hpair
        exact .inl ⟨rfl, by rw [hrest]⟩
      · exact .inr hsome

/-! ## Against an honest tree -/

/-- A pair offered for honest node `(level + 1, j)` in place of its children. -/
structure SecondPreimage (α : Type) where
  /-- The level of the children. -/
  level : Nat
  /-- The index of the parent on level `level + 1`. -/
  j : Nat
  /-- The pair, left child first. -/
  y : α × α

/-- The pair is not the honest children, and hashes to the honest node. -/
def SecondPreimage.Valid (leaves : Nat → Id α) (w : SecondPreimage α) : Prop :=
  w.y ≠ ((node hash leaves w.level (2 * w.j)).run, (node hash leaves w.level (2 * w.j + 1)).run) ∧
    (hash (w.level + 1) w.j w.y.1 w.y.2).run = (node hash leaves (w.level + 1) w.j).run

/-- The second preimage a climb from `(level, j)` runs into, at the lowest level where one exists.

On each level, the climb hashes its held node with its sibling, in the order the index gives.

A level where that pair is not the honest one but the parent is honest is a second preimage. -/
def findSecondPreimage [DecidableEq α] (leaves : Nat → Id α) :
    (level j : Nat) → (b : α) → (q : List α) → Option (SecondPreimage α)
  | level, j, b, t :: q =>
    let y := ordered j b t
    let parent := (hash (level + 1) (j / 2) y.1 y.2).run
    if y ≠ ((node hash leaves level (2 * (j / 2))).run, (node hash leaves level (2 * (j / 2) + 1)).run) ∧
        parent = (node hash leaves (level + 1) (j / 2)).run then
      some ⟨level, j / 2, y⟩
    else findSecondPreimage leaves (level + 1) (j / 2) parent q
  | _, _, _, [] => none

/-- Every second preimage `findSecondPreimage` returns is valid, for an ancestor of `(level, j)`.

The ancestor is `k + 1` levels up, at index `j / 2^(k + 1)`. -/
theorem findSecondPreimage_valid [DecidableEq α] (leaves : Nat → Id α) :
    ∀ (q : List α) (level j : Nat) (b : α) (w : SecondPreimage α),
      findSecondPreimage hash leaves level j b q = some w →
      w.Valid hash leaves ∧ ∃ k < q.length, w.level = level + k ∧ w.j = j / 2 ^ (k + 1) := by
  intro q
  induction q with
  | nil => intro level j b w h; simp [findSecondPreimage] at h
  | cons t rest ih =>
    intro level j b w h
    simp only [findSecondPreimage] at h
    split at h
    · -- This level is the second preimage.
      rename_i hfound
      cases h
      exact ⟨hfound, 0, by simp, rfl, by simp⟩
    · -- The second preimage is further up: one level higher in the count.
      obtain ⟨hvalid, k, hk, hlevel, hj⟩ := ih (level + 1) (j / 2) _ w h
      refine ⟨hvalid, k + 1, by simpa using hk, by omega, ?_⟩
      rw [hj, div_two_div_pow]

/-- Binding against an honest tree: a climb from `(level, j)` over `n` siblings that reaches the honest ancestor is honest.

Otherwise `findSecondPreimage` finds a second preimage, valid by `findSecondPreimage_valid`. -/
theorem climb_binding_node [DecidableEq α] (leaves : Nat → Id α) :
    ∀ (n level j : Nat) (b : α) (q : List α), q.length = n →
      (climb hash level j b q).run = (node hash leaves (level + n) (j / 2 ^ n)).run →
      (b = (node hash leaves level j).run ∧ q = (siblings hash leaves level j n).run.toList) ∨
        (findSecondPreimage hash leaves level j b q).isSome := by
  intro n
  induction n with
  | zero =>
    intro level j b q hl heq
    -- No sibling: the climb is its start, which must be the honest node.
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    exact .inl ⟨by simpa using heq, by simp [siblings]⟩
  | succ n ih =>
    intro level j b q hl heq
    cases q with
    | nil => simp at hl
    | cons t rest =>
      rw [climb_cons, ← div_two_div_pow, show level + (n + 1) = level + 1 + n by omega] at heq
      simp only [findSecondPreimage]
      -- The honest children, in order, are the honest node and its sibling.
      have honest := ordered_sibling (fun i => (node hash leaves level i).run) j
      -- When this level is a second preimage, the search stops here.
      by_cases hfound : ordered j b t
            ≠ ((node hash leaves level (2 * (j / 2))).run, (node hash leaves level (2 * (j / 2) + 1)).run) ∧
          (hash (level + 1) (j / 2) (ordered j b t).1 (ordered j b t).2).run
            = (node hash leaves (level + 1) (j / 2)).run
      · exact .inr (by simp [hfound])
      simp only [hfound, ↓reduceIte]
      rcases ih (level + 1) (j / 2) _ rest (by simpa using hl) heq with
        ⟨hparent, hrest⟩ | hsome
      · -- An honest parent and no second preimage here: the pair is the honest one.
        have hpair : ordered j b t
            = ordered j (node hash leaves level j).run (node hash leaves level (j ^^^ 1)).run := by
          rw [honest]
          exact Classical.byContradiction fun hne => hfound ⟨hne, hparent⟩
        obtain ⟨rfl, rfl⟩ := ordered_inj.mp hpair
        exact .inl ⟨rfl, by rw [siblings_succ_toList, hrest]⟩
      · exact .inr hsome

end EthLib.Cryptography.Merkle
