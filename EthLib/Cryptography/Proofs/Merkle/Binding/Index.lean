module

public import EthLib.Cryptography.Proofs.Merkle.Binding.Collision
public import EthLib.Cryptography.Proofs.Merkle.Binding.SecondPreimage

/-!
# Proofs: a path binds its leaf index and its length

Two attacks change the index or the length of a path instead of its leaf:

- the path of leaf `j` presented at index `j + 2^h`;
- an interior node presented as a leaf, with the shorter path of its position.

If the hash reads the position, a climb that reaches the root of height `h` has the honest shape.

It starts below `2^h` with `h` siblings, or the search finds a collision across two positions.

With the second-preimage search, a climb that reaches the root is the honest opening.

Otherwise one of the two searches succeeds.

If the hash ignores the position, that collision is free and both attacks succeed.

The verifier must then check `j < 2^h` and the length.

Separating leaves from nodes, as [RFC 6962][rfc] does, also stops the second attack.

A climb with no hash call is not covered: an empty path, or a tree of height 0.

[rfc]: https://www.rfc-editor.org/rfc/rfc6962#section-2.1
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle

variable {α : Type} (hash : Position → α → α → Id α)

/-- A climb with a sibling ends with the hash of its last pair, `t.length` levels above `p`. -/
theorem climb_eq_hash_getLast :
    ∀ (t : List α) (p : Position) (b : α), t ≠ [] →
      ∃ x, (climbPairs hash p b t).getLast? = some x ∧
        (climb hash p b t).run = (hash (p.ancestor t.length) x.1 x.2).run := by
  intro t
  induction t with
  | nil => intro p b ht; exact absurd rfl ht
  | cons u rest ih =>
    intro p b _
    cases rest with
    | nil => exact ⟨ordered p b u, by simp [climbPairs], by simp [climb_cons]⟩
    | cons v rest' =>
      -- The last call is that of the climb from the parent.
      obtain ⟨x, hx, hclimb⟩ := ih p.parent _ (List.cons_ne_nil v rest')
      refine ⟨x, ?_, ?_⟩
      · simp only [climbPairs] at hx ⊢
        simpa using hx
      · rw [climb_cons, hclimb, Position.ancestor_parent]
        rfl

/-! ## With the position in the hash -/

/-- Two inputs of the node hash, each a position and a pair: a candidate collision. -/
structure PositionCollision (α : Type) where
  /-- The first input: a position and the pair hashed there. -/
  x : Position × α × α
  /-- The second input: a position and the pair hashed there. -/
  y : Position × α × α

/-- The two inputs differ and have one output. -/
def PositionCollision.Valid (c : PositionCollision α) : Prop :=
  c.x ≠ c.y ∧ (hash c.x.1 c.x.2.1 c.x.2.2).run = (hash c.y.1 c.y.2.1 c.y.2.2).run

/-- The last call of a climb and the root's call, if their positions differ and outputs agree. -/
def findPositionCollision [DecidableEq α] (leaves : Nat → Id α) (h : Nat) (p : Position) (b : α)
    (t : List α) : Option (PositionCollision α) :=
  match (climbPairs hash p b t).getLast?, h with
  | some x, level + 1 =>
    let top : Position × α × α := (p.ancestor t.length, x)
    let root : Position × α × α :=
      (⟨level + 1, 0⟩, (node hash leaves ⟨level, 0⟩).run, (node hash leaves ⟨level, 1⟩).run)
    if top.1 ≠ root.1 ∧
        (hash top.1 top.2.1 top.2.2).run = (hash root.1 root.2.1 root.2.2).run then
      some ⟨top, root⟩
    else none
  | _, _ => none

/-- What the search returns is a valid collision, at two different positions. -/
theorem findPositionCollision_valid [DecidableEq α] (leaves : Nat → Id α) (h : Nat)
    (p : Position) (b : α) (t : List α) (c : PositionCollision α)
    (found : findPositionCollision hash leaves h p b t = some c) :
    c.Valid hash ∧ c.x.1 ≠ c.y.1 := by
  unfold findPositionCollision at found
  split at found
  · simp only at found
    split at found
    · rename_i hfound
      cases found
      exact ⟨⟨fun heq => hfound.1 (congrArg Prod.fst heq), hfound.2⟩, hfound.1⟩
    · cases found
  · cases found

/-- The search finds nothing on a climb of the honest shape: from `j < 2^h`, with `h` siblings. -/
theorem findPositionCollision_of_length [DecidableEq α] (leaves : Nat → Id α) {h j : Nat}
    (hj : j < 2 ^ h) (b : α) (t : List α) (ht : t.length = h) :
    findPositionCollision hash leaves h ⟨0, j⟩ b t = none := by
  unfold findPositionCollision
  split
  · -- The last call is at level `h` and index `j / 2^h = 0`: the root's position.
    simp [ht, Position.ancestor_mk_zero, Nat.div_eq_of_lt hj]
  · rfl

/-- A climb that reaches the root has the honest shape, or yields a collision across positions.

Against a verifier that checks the length, its content is the bound `j < 2^h`. -/
theorem climb_root_position [DecidableEq α] (leaves : Nat → Id α) {h j : Nat} (b : α)
    (t : List α) (hh : h ≠ 0) (ht : t ≠ [])
    (reach : (climb hash ⟨0, j⟩ b t).run = (root hash leaves h).run) :
    (t.length = h ∧ j < 2 ^ h) ∨ (findPositionCollision hash leaves h ⟨0, j⟩ b t).isSome := by
  obtain ⟨level, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh
  obtain ⟨x, hx, hclimb⟩ := climb_eq_hash_getLast hash t ⟨0, j⟩ b ht
  -- The climb's last call is at the root's position, or at another one.
  by_cases hpos : (⟨0, j⟩ : Position).ancestor t.length = ⟨level + 1, 0⟩
  · -- Level `t.length = h` and index `j / 2^h = 0`, so `j < 2^h`.
    rw [Position.ancestor_mk_zero, Position.mk.injEq] at hpos
    obtain ⟨hlength, hindex⟩ := hpos
    refine .inl ⟨hlength, ?_⟩
    rw [hlength] at hindex
    exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).mp hindex
  · refine .inr ?_
    have hroot := node_succ_run hash leaves level 0
    simp only [Nat.mul_zero, Nat.zero_add] at hroot
    -- The two calls have one output, the root.
    have hout := hclimb.symm.trans (reach.trans hroot)
    unfold findPositionCollision
    rw [hx]
    simp only [ne_eq, hpos, not_false_eq_true, hout, and_self, ↓reduceIte, Option.isSome_some]

/-- For a hash injective on the position and the pair, the search returns nothing.

So whether the search succeeds depends on the hash. -/
theorem findPositionCollision_injective [DecidableEq α]
    (inj : ∀ (p q : Position) (x y : α × α),
      (hash p x.1 x.2).run = (hash q y.1 y.2).run → p = q ∧ x = y)
    (leaves : Nat → Id α) (h : Nat) (p : Position) (b : α) (t : List α) :
    findPositionCollision hash leaves h p b t = none := by
  cases found : findPositionCollision hash leaves h p b t with
  | none => rfl
  | some c =>
    obtain ⟨⟨-, hout⟩, hpos⟩ := findPositionCollision_valid hash leaves h p b t c found
    exact absurd (inj _ _ _ _ hout).1 hpos

/-- A climb that reaches the root is the honest opening, or a second preimage, or a collision. -/
theorem climb_root_honest [DecidableEq α] (leaves : Nat → Id α) {h j : Nat} (b : α)
    (t : List α) (hh : h ≠ 0) (ht : t ≠ [])
    (reach : (climb hash ⟨0, j⟩ b t).run = (root hash leaves h).run) :
    (j < 2 ^ h ∧ t.length = h ∧ b = (leaves j).run ∧ t = (path hash leaves h j).run.toList) ∨
      (findSecondPreimage hash leaves ⟨0, j⟩ b t).isSome ∨
      (findPositionCollision hash leaves h ⟨0, j⟩ b t).isSome := by
  rcases climb_root_position hash leaves b t hh ht reach with ⟨hlength, hj⟩ | hsome
  · -- In range, the ancestor of leaf `j` on level `h` is the root.
    have hnode : (climb hash ⟨0, j⟩ b t).run
        = (node hash leaves ((⟨0, j⟩ : Position).ancestor h)).run := by
      rw [Position.ancestor_eq_of_index_lt (p := ⟨0, j⟩) hj, reach]
      simp only [Nat.zero_add]
      rfl
    rcases climb_binding_node hash leaves h ⟨0, j⟩ b t hlength hnode with ⟨hb, hpath⟩ | hsecond
    · exact .inl ⟨hj, hlength, hb, hpath⟩
    · exact .inr (.inl hsecond)
  · exact .inr (.inr hsome)

/-! ## Without the position in the hash -/

/-- With a hash that ignores the position, a climb reads only its index modulo `2^n`. -/
theorem climb_const_congr (combine : α → α → Id α) :
    ∀ (s : List α) (l l' i i' : Nat) (a : α), i % 2 ^ s.length = i' % 2 ^ s.length →
      (climb (fun _ => combine) ⟨l, i⟩ a s).run = (climb (fun _ => combine) ⟨l', i'⟩ a s).run := by
  intro s
  induction s with
  | nil => intro l l' i i' a _; rfl
  | cons u rest ih =>
    intro l l' i i' a hmod
    rw [List.length_cons, Nat.pow_succ'] at hmod
    -- Same parity, so the same order of the pair.
    have hparity : i % 2 = i' % 2 := by
      rw [← Nat.mod_mul_right_mod i 2 (2 ^ rest.length),
        ← Nat.mod_mul_right_mod i' 2 (2 ^ rest.length), hmod]
    have horder : ordered ⟨l, i⟩ a u = ordered ⟨l', i'⟩ a u := by
      simp only [ordered_eq_ite, hparity]
    -- The parents agree modulo `2^(n - 1)`.
    have hparent : i / 2 % 2 ^ rest.length = i' / 2 % 2 ^ rest.length := by
      rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self, hmod]
    rw [climb_cons, climb_cons, horder]
    exact ih _ _ _ _ _ hparent

/-- With a hash that ignores the position, index `j + 2^n` climbs as index `j`. -/
theorem climb_const_shift (combine : α → α → Id α) (j : Nat) (a : α) (s : List α) :
    (climb (fun _ => combine) ⟨0, j + 2 ^ s.length⟩ a s).run
      = (climb (fun _ => combine) ⟨0, j⟩ a s).run :=
  climb_const_congr combine s 0 0 _ _ a (by simp)

/-- With a hash that ignores the position, the path of leaf `j` also opens index `j + 2^h`. -/
theorem climb_const_shift_root (combine : α → α → Id α) (leaves : Nat → Id α) {h j : Nat}
    (hj : j < 2 ^ h) :
    (climb (fun _ => combine) ⟨0, j + 2 ^ h⟩ (leaves j).run
        (path (fun _ => combine) leaves h j).run.toList).run
      = (root (fun _ => combine) leaves h).run := by
  have := climb_const_shift combine j (leaves j).run (path (fun _ => combine) leaves h j).run.toList
  simp only [Vector.length_toList] at this
  rw [this, climb_path_root _ leaves hj]

/-- With a hash that ignores the position, node `(k, i)` opens as leaf `i` with `h - k` siblings. -/
theorem climb_const_interior (combine : α → α → Id α) (leaves : Nat → Id α) {k h i : Nat}
    (hk : k ≤ h) (hi : i < 2 ^ (h - k)) :
    (climb (fun _ => combine) ⟨0, i⟩ (node (fun _ => combine) leaves ⟨k, i⟩).run
        (siblings (fun _ => combine) leaves ⟨k, i⟩ (h - k)).run.toList).run
      = (root (fun _ => combine) leaves h).run := by
  -- The climb never reads the level.
  rw [climb_const_congr combine _ 0 k i i _ rfl, climb_siblings,
    Position.ancestor_eq_of_index_lt (p := ⟨k, i⟩) hi]
  simp only [Nat.add_sub_cancel' hk]
  rfl

/-- With a hash that ignores the position, the search succeeds on the shifted path of a leaf.

So the collision across positions is free for such a hash. -/
theorem findPositionCollision_const_shift [DecidableEq α] (combine : α → α → Id α)
    (leaves : Nat → Id α) {h j : Nat} (hh : h ≠ 0) (hj : j < 2 ^ h) :
    (findPositionCollision (fun _ => combine) leaves h ⟨0, j + 2 ^ h⟩ (leaves j).run
      (path (fun _ => combine) leaves h j).run.toList).isSome := by
  have ht : (path (fun _ => combine) leaves h j).run.toList ≠ [] := by
    rw [ne_eq, ← List.length_eq_zero_iff, Vector.length_toList]
    exact hh
  -- The shifted index `j + 2^h` is not below `2^h`.
  rcases climb_root_position _ leaves _ _ hh ht (climb_const_shift_root combine leaves hj) with
    ⟨-, hout⟩ | hsome
  · omega
  · exact hsome

end EthLib.Cryptography.Merkle
