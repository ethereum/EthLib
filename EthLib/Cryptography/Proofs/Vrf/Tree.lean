import EthLib.Cryptography.Vrf.Tree

/-!
# Proofs: `Vrf.Tree`

The two guarantees of a Merkle tree, for every node type and node hash.

- Completeness: the path of leaf `i` leads from that leaf to the root.
- Binding: two openings of one index that lead to one root are equal, or the node hash collides.
-/

namespace EthLib.Cryptography.Vrf.Tree

variable {α : Type} (hash : α → α → α)

/-- Two different child pairs with one parent. -/
def Collision : Prop :=
  ∃ x y : α × α, x ≠ y ∧ hash x.1 x.2 = hash y.1 y.2

/-- Every node above level 0 is the hash of its two children. -/
theorem node_succ (leaves : Nat → α) (l j : Nat) :
    node hash leaves (l + 1) j = hash (node hash leaves l (2 * j)) (node hash leaves l (2 * j + 1)) :=
  rfl

/-! ## Completeness -/

/-- Flipping the bottom bit, written as arithmetic. -/
private theorem xor_one (n : Nat) : n ^^^ 1 = 2 * (n / 2) + (1 - n % 2) := by
  -- The bits above the bottom one are untouched.
  have hd : (n ^^^ 1) / 2 = n / 2 := by rw [Nat.xor_div_two]; simp
  -- The bottom one is swapped.
  have hm : (n ^^^ 1) % 2 = 1 ↔ n % 2 = 0 := by simp
  have h1 := Nat.mod_two_eq_zero_or_one n
  have h2 := Nat.mod_two_eq_zero_or_one (n ^^^ 1)
  omega

/-- Climbing the honest siblings from leaf `i`'s ancestor on level `k` reaches its ancestor `n` levels up. -/
theorem climb_siblings (leaves : Nat → α) (i : Nat) :
    ∀ n k, climb hash (i >>> k) (node hash leaves k (i >>> k)) (siblings hash leaves i k n)
      = node hash leaves (k + n) (i >>> (k + n)) := by
  intro n
  induction n with
  | zero => intro k; rfl
  | succ n ih =>
    intro k
    simp only [siblings, climb]
    -- Halving the index moves to the ancestor one level up.
    have hs : i >>> k / 2 = i >>> (k + 1) := (Nat.shiftRight_succ _ _).symm
    rw [hs]
    -- The held node and its sibling are the two children of that ancestor.
    have hstep : (if i >>> k % 2 = 0 then
          hash (node hash leaves k (i >>> k)) (node hash leaves k ((i >>> k) ^^^ 1))
        else hash (node hash leaves k ((i >>> k) ^^^ 1)) (node hash leaves k (i >>> k)))
        = node hash leaves (k + 1) (i >>> (k + 1)) := by
      simp only [node]
      rw [← hs, xor_one]
      rcases Nat.mod_two_eq_zero_or_one (i >>> k) with hr | hr
      · simp only [hr, ite_true]
        congr 2 <;> omega
      · simp only [hr]
        simp
        congr 2 <;> omega
    rw [hstep, ih (k + 1), show k + 1 + n = k + (n + 1) by omega]

/-- Completeness: the path of a leaf `i < 2^h` leads from that leaf to the root. -/
theorem climb_path (h : Nat) (leaves : Nat → α) {i : Nat} (hi : i < 2 ^ h) :
    climb hash i (leaves i) (path hash h leaves i).toList = root hash h leaves := by
  have := climb_siblings hash leaves i h 0
  simp only [Nat.shiftRight_zero, Nat.zero_add] at this
  -- Leaf `i` sits below the root, so its ancestor on level `h` is node 0.
  rw [show (path hash h leaves i).toList = siblings hash leaves i 0 h from rfl,
    show leaves i = node hash leaves 0 i from rfl, this, root, Nat.shiftRight_eq_div_pow,
    Nat.div_eq_of_lt hi]

/-! ## Binding -/

/-- Binding: two climbs from one index over equally many siblings that meet are equal, or the hash collides. -/
theorem climb_binding {i : Nat} {a b : α} {p q : List α} (hl : p.length = q.length)
    (heq : climb hash i a p = climb hash i b q) : (a = b ∧ p = q) ∨ Collision hash := by
  induction p generalizing i a b q with
  | nil =>
    cases q with
    | nil => exact .inl ⟨heq, rfl⟩
    | cons _ _ => simp at hl
  | cons s rest ih =>
    cases q with
    | nil => simp at hl
    | cons t rest' =>
      simp only [climb] at heq
      -- The two pairs of children hashed on this level, in tree order.
      let x := if i % 2 = 0 then (a, s) else (s, a)
      let y := if i % 2 = 0 then (b, t) else (t, b)
      by_cases hxy : x = y
      · -- Equal pairs: the held nodes and the siblings agree, and so do the climbs above.
        have hab : a = b ∧ s = t := by
          by_cases hi : i % 2 = 0 <;> simp_all [x, y, Prod.ext_iff]
        obtain ⟨rfl, rfl⟩ := hab
        rcases ih (by simpa using hl) heq with ⟨-, hr⟩ | hcol
        · exact .inl ⟨rfl, by rw [hr]⟩
        · exact .inr hcol
      · by_cases hparent : (if i % 2 = 0 then hash a s else hash s a)
            = (if i % 2 = 0 then hash b t else hash t b)
        · -- Different pairs with one parent: a collision on this level.
          refine .inr ⟨x, y, hxy, ?_⟩
          by_cases hi : i % 2 = 0 <;> simp_all [x, y]
        · -- Different parents: the climbs above must collide to meet.
          rcases ih (by simpa using hl) heq with ⟨hp, -⟩ | hcol
          · exact absurd hp hparent
          · exact .inr hcol

end EthLib.Cryptography.Vrf.Tree
