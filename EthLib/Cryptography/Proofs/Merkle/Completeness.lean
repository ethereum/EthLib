module

public import EthLib.Cryptography.Merkle.Tree

/-!
# Proofs: completeness of `Merkle.Tree`

Completeness: climbing from a leaf with its path reaches the root.

The statements hold for every node hash, run in the identity monad.

The unfolding equations of a node hold in every monad.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle

/-! ## Unfolding, in any monad -/

section Monad

variable {m : Type → Type} [Monad m] {α : Type} (hash : Nat → Nat → α → α → m α)

/-- A node on level 0 is a leaf. -/
theorem node_zero (leaves : Nat → m α) (j : Nat) : node hash leaves 0 j = leaves j :=
  rfl

/-- A node above level 0 hashes its two children at its own position, the left subtree first. -/
theorem node_succ (leaves : Nat → m α) (level j : Nat) :
    node hash leaves (level + 1) j = (do
      let left ← node hash leaves level (2 * j)
      let right ← node hash leaves level (2 * j + 1)
      hash (level + 1) j left right) :=
  rfl

/-- Climbing two lists of siblings in turn climbs the first, then the second from where it ends. -/
theorem climb_append [LawfulMonad m] :
    ∀ (p q : List α) (level j : Nat) (current : α),
      climb hash level j current (p ++ q) = (do
        let middle ← climb hash level j current p
        climb hash (level + p.length) (j / 2 ^ p.length) middle q)
  | [], q, level, j, current => by simp [climb]
  | sibling :: rest, q, level, j, current => by
    simp only [List.cons_append, climb, List.length_cons]
    -- One level up, the rest of the climb starts at the same position.
    have position : j / 2 / 2 ^ rest.length = j / 2 ^ (rest.length + 1) := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
    have level_up : level + 1 + rest.length = level + (rest.length + 1) := by omega
    split <;> simp only [bind_assoc, climb_append rest q, position, level_up]

/-- Climbing the first `n + 1` siblings climbs the first `n`, then hashes in sibling `n`.

The held node is then at `(n, j / 2^n)`, so bit `n` of `j` says which child it is. -/
theorem climb_take_succ [LawfulMonad m] (j : Nat) (current : α) (p : List α) (n : Nat)
    (hn : n < p.length) :
    climb hash 0 j current (p.take (n + 1)) = (do
      let held ← climb hash 0 j current (p.take n)
      if j / 2 ^ n % 2 = 0 then hash (n + 1) (j / 2 ^ n / 2) held p[n]
        else hash (n + 1) (j / 2 ^ n / 2) p[n] held) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hn, Option.toList_some, climb_append,
    List.length_take_of_le (Nat.le_of_lt hn)]
  simp only [Nat.zero_add, climb, bind_pure]

end Monad

/-! ## Unfolding, in the identity monad -/

variable {α : Type} (hash : Nat → Nat → α → α → Id α)

/-- A node above level 0 is the hash of its two children, at its own position. -/
theorem node_succ_run (leaves : Nat → Id α) (level j : Nat) :
    (node hash leaves (level + 1) j).run
      = (hash (level + 1) j (node hash leaves level (2 * j)).run
          (node hash leaves level (2 * j + 1)).run).run :=
  rfl

/-- The siblings start with the sibling of the node, then go on one level up. -/
theorem siblings_succ_toList (leaves : Nat → Id α) (level j n : Nat) :
    (siblings hash leaves level j (n + 1)).run.toList
      = (node hash leaves level (j ^^^ 1)).run
          :: (siblings hash leaves (level + 1) (j / 2) n).run.toList := by
  simp [siblings, Vector.toList_cast]

/-- Climbing with no sibling stays put. -/
@[simp] theorem climb_nil (level j : Nat) (current : α) :
    (climb hash level j current []).run = current :=
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
    (climb hash level j current (sibling :: rest)).run
      = (climb hash (level + 1) (j / 2)
          (hash (level + 1) (j / 2) (ordered j current sibling).1
            (ordered j current sibling).2).run rest).run := by
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
theorem climb_siblings (leaves : Nat → Id α) :
    ∀ n level j,
      (climb hash level j (node hash leaves level j).run
          (siblings hash leaves level j n).run.toList).run
        = (node hash leaves (level + n) (j / 2 ^ n)).run := by
  intro n
  induction n with
  | zero => intro level j; simp [siblings]
  | succ n ih =>
    intro level j
    -- The held node and its sibling are the children of the parent, so the step reaches it.
    rw [siblings_succ_toList, climb_cons, ordered_sibling (fun i => (node hash leaves level i).run)]
    dsimp only
    rw [← node_succ_run hash leaves level (j / 2), ih, div_two_div_pow, Nat.add_assoc,
      Nat.add_comm 1 n]

/-- Climbing from leaf `j` with its path reaches its ancestor on level `h`. -/
theorem climb_path (leaves : Nat → Id α) (h j : Nat) :
    (climb hash 0 j (leaves j).run (path hash leaves h j).run.toList).run
      = (node hash leaves h (j / 2 ^ h)).run := by
  have := climb_siblings hash leaves h 0 j
  rwa [Nat.zero_add] at this

/-- Completeness: climbing from a leaf `j < 2^h` with its path reaches the root. -/
theorem climb_path_root (leaves : Nat → Id α) {h j : Nat} (hj : j < 2 ^ h) :
    (climb hash 0 j (leaves j).run (path hash leaves h j).run.toList).run
      = (root hash leaves h).run := by
  rw [climb_path, Nat.div_eq_of_lt hj]
  rfl

/-! ## Trees that ignore the position -/

/-- In a tree that hashes every node alike, a node is the root of the subtree below it.

The subtree's leaves are the `2^level` leaves under node `j`, starting at leaf `j * 2^level`. -/
theorem node_const_shift (combine : α → α → Id α) :
    ∀ (level : Nat) (leaves : Nat → Id α) (j : Nat),
      (node (fun _ _ => combine) leaves level j).run
        = (node (fun _ _ => combine) (fun t => leaves (j * 2 ^ level + t)) level 0).run := by
  intro level
  induction level with
  | zero => intro leaves j; simp [node]
  | succ l ih =>
    intro leaves j
    simp only [node_succ_run, Nat.mul_zero, Nat.zero_add]
    -- Both children are roots of subtrees, the right one starting `2^l` leaves later.
    rw [ih leaves (2 * j), ih leaves (2 * j + 1), ih _ 0, ih _ 1]
    have left : (fun t => leaves (2 * j * 2 ^ l + (0 * 2 ^ l + t)))
        = fun t => leaves (j * 2 ^ (l + 1) + t) := by
      funext t
      rw [Nat.pow_succ, Nat.zero_mul, Nat.zero_add, Nat.mul_comm 2 j, Nat.mul_assoc, Nat.mul_comm 2]
    have right : (fun t => leaves ((2 * j + 1) * 2 ^ l + t))
        = fun t => leaves (j * 2 ^ (l + 1) + (1 * 2 ^ l + t)) := by
      funext t
      rw [Nat.pow_succ, Nat.add_mul, Nat.one_mul, Nat.mul_comm 2 j, Nat.mul_assoc, Nat.mul_comm 2,
        Nat.add_assoc]
    rw [left, right]

end EthLib.Cryptography.Merkle
