import EthLib.Cryptography.Merkle.Tree

/-!
# Proofs: `Merkle.Tree`

Completeness: climbing from a leaf with its path reaches the root.

The statements hold for every node hash.
-/

namespace EthLib.Cryptography.Merkle

variable {α : Type} (hash : Nat → Nat → α → α → α)

/-! ## Unfolding -/

/-- A node on level 0 is a leaf. -/
@[simp] theorem node_zero (leaves : Nat → α) (j : Nat) : node hash leaves 0 j = leaves j :=
  rfl

/-- A node above level 0 is the hash of its two children, at its own position. -/
theorem node_succ (leaves : Nat → α) (level j : Nat) :
    node hash leaves (level + 1) j
      = hash (level + 1) j (node hash leaves level (2 * j)) (node hash leaves level (2 * j + 1)) :=
  rfl

/-- Climbing with no sibling stays put. -/
@[simp] theorem climb_nil (level j : Nat) (current : α) : climb hash level j current [] = current :=
  rfl

/-- The two children a climb step hashes, the left one first.

The low bit of `j` says whether the held node is the left one. -/
def ordered (j : Nat) (current sibling : α) : α × α :=
  if j % 2 = 0 then (current, sibling) else (sibling, current)

/-- The pair of children determines the held node and its sibling. -/
theorem ordered_inj {j : Nat} {c s c' s' : α} :
    ordered j c s = ordered j c' s' ↔ c = c' ∧ s = s' := by
  unfold ordered
  split <;> simp only [Prod.mk.injEq, and_comm]

/-- One climb step: hash the children in order at the parent's position, then go on from there. -/
theorem climb_cons (level j : Nat) (current sibling : α) (rest : List α) :
    climb hash level j current (sibling :: rest)
      = climb hash (level + 1) (j / 2)
          (hash (level + 1) (j / 2) (ordered j current sibling).1 (ordered j current sibling).2)
          rest := by
  simp only [climb, ordered]
  split <;> rfl

/-! ## Completeness -/

/-- Halving an index, then dividing by `2^n`, divides it by `2^(n + 1)`. -/
theorem div_two_div_pow (j n : Nat) : j / 2 / 2 ^ n = j / 2 ^ (n + 1) := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

/-- Flipping the low bit, written as arithmetic. -/
private theorem xor_one (n : Nat) : n ^^^ 1 = 2 * (n / 2) + (1 - n % 2) := by
  -- The bits above the low one are untouched.
  have hd : (n ^^^ 1) / 2 = n / 2 := by rw [Nat.xor_div_two]; simp
  -- The low one is swapped.
  have hm : (n ^^^ 1) % 2 = 1 ↔ n % 2 = 0 := by simp
  have h1 := Nat.mod_two_eq_zero_or_one n
  have h2 := Nat.mod_two_eq_zero_or_one (n ^^^ 1)
  omega

/-- A node and its sibling, in order, are the two children of their parent.

Here `f` reads one level of a tree. -/
theorem ordered_sibling (f : Nat → α) (j : Nat) :
    ordered j (f j) (f (j ^^^ 1)) = (f (2 * (j / 2)), f (2 * (j / 2) + 1)) := by
  unfold ordered
  rw [xor_one]
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  · -- An even node is the left child, and its sibling the right one.
    simp only [hj, ite_true]
    congr 2 <;> omega
  · -- An odd node is the right child, and its sibling the left one.
    simp only [hj]
    simp
    congr 2 <;> omega

/-- Climbing from a node with the siblings of its ancestors reaches its ancestor `n` levels up. -/
theorem climb_siblings (leaves : Nat → α) :
    ∀ n level j, climb hash level j (node hash leaves level j) (siblings hash leaves level j n)
      = node hash leaves (level + n) (j / 2 ^ n) := by
  intro n
  induction n with
  | zero => intro level j; simp [siblings]
  | succ n ih =>
    intro level j
    -- The held node and its sibling are the children of the parent, so the step reaches it.
    rw [siblings, climb_cons, ordered_sibling (node hash leaves level)]
    dsimp only
    rw [← node_succ hash leaves level (j / 2), ih, div_two_div_pow, Nat.add_assoc, Nat.add_comm 1 n]

/-- Climbing from leaf `j` with its path reaches its ancestor on level `h`. -/
theorem climb_path (leaves : Nat → α) (h j : Nat) :
    climb hash 0 j (leaves j) (path hash leaves h j).toList = node hash leaves h (j / 2 ^ h) := by
  have := climb_siblings hash leaves h 0 j
  rwa [Nat.zero_add] at this

/-- Completeness: climbing from a leaf `j < 2^h` with its path reaches the root. -/
theorem climb_path_root (leaves : Nat → α) {h j : Nat} (hj : j < 2 ^ h) :
    climb hash 0 j (leaves j) (path hash leaves h j).toList = root hash leaves h := by
  rw [climb_path, Nat.div_eq_of_lt hj]
  rfl

/-! ## Trees that ignore the position -/

/-- In a tree that hashes every node alike, a node is the root of the subtree below it.

The subtree's leaves are the `2^level` leaves under node `j`, starting at leaf `j * 2^level`. -/
theorem node_const_shift (combine : α → α → α) :
    ∀ (level : Nat) (leaves : Nat → α) (j : Nat),
      node (fun _ _ => combine) leaves level j
        = node (fun _ _ => combine) (fun t => leaves (j * 2 ^ level + t)) level 0 := by
  intro level
  induction level with
  | zero => intro leaves j; simp
  | succ l ih =>
    intro leaves j
    simp only [node]
    -- Both children are roots of subtrees, the right one starting `2^l` leaves later.
    rw [ih leaves (2 * j), ih leaves (2 * j + 1), ih _ 0, ih _ 1]
    congr 2 <;> funext t <;> congr 1
    · rw [Nat.pow_succ]
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [Nat.mul_comm 2 j, Nat.mul_assoc, Nat.mul_comm 2]
    · rw [Nat.pow_succ, Nat.add_mul, Nat.one_mul, Nat.mul_comm 2 j, Nat.mul_assoc, Nat.mul_comm 2,
        Nat.add_assoc]

end EthLib.Cryptography.Merkle
