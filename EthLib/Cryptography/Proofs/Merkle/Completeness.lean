module

public import EthLib.Cryptography.Merkle.Tree

/-!
# Proofs: completeness of Merkle trees

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
    simp only [bind_assoc, climb_append rest q, position, level_up]

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
  -- The order of the children is the one the bit gives.
  refine congrArg _ (funext fun held => ?_)
  unfold ordered
  split <;> rfl

/-- Ordering two mapped children maps the ordered pair. -/
theorem ordered_map {β : Type} (f : α → β) (j : Nat) (current sibling : α) :
    ordered j (f current) (f sibling) = Prod.map f f (ordered j current sibling) := by
  unfold ordered
  split <;> rfl

/-- A map that commutes with the node hash commutes with the climb. -/
theorem climb_map [LawfulMonad m] {β : Type} (hash' : Nat → Nat → β → β → m β) (f : α → β)
    (commute : ∀ level j left right,
      hash' level j (f left) (f right) = f <$> hash level j left right) :
    ∀ (siblings : List α) (level j : Nat) (current : α),
      climb hash' level j (f current) (siblings.map f) = f <$> climb hash level j current siblings
  | [], _, _, _ => by simp [climb]
  | sibling :: rest, level, j, current => by
    simp only [List.map_cons, climb, ordered_map, Prod.map_fst, Prod.map_snd, commute,
      bind_map_left, map_bind, climb_map hash' f commute rest]

/-! ## The levels a tree hashes at -/

/-- A node on `level` hashes only at levels 1 to `level`.

So two node hashes that agree there give the same node. -/
theorem node_congr (hash' : Nat → Nat → α → α → m α) (leaves : Nat → m α) :
    ∀ (level j : Nat), (∀ k, 1 ≤ k → k ≤ level → hash k = hash' k) →
      node hash leaves level j = node hash' leaves level j
  | 0, _, _ => rfl
  | level + 1, j, agree => by
    -- The children agree by induction, and the node's own hash is at `level + 1`.
    have below : ∀ k, 1 ≤ k → k ≤ level → hash k = hash' k := fun k h1 h2 => agree k h1 (by omega)
    rw [node_succ, node_succ, node_congr hash' leaves level (2 * j) below,
      node_congr hash' leaves level (2 * j + 1) below, agree (level + 1) (by omega) (Nat.le_refl _)]

/-- The `n` siblings from `level` up hash only at levels 1 to `level + n - 1`. -/
theorem siblings_congr (hash' : Nat → Nat → α → α → m α) (leaves : Nat → m α) :
    ∀ (n level j : Nat), (∀ k, 1 ≤ k → k < level + n → hash k = hash' k) →
      siblings hash leaves level j n = siblings hash' leaves level j n
  | 0, _, _, _ => rfl
  | n + 1, level, j, agree => by
    -- The first sibling is a node on `level`, and the rest start one level up.
    simp only [siblings]
    rw [node_congr hash hash' leaves level (j ^^^ 1) (fun k h1 h2 => agree k h1 (by omega)),
      siblings_congr hash' leaves n (level + 1) (j / 2) (fun k h1 h2 => agree k h1 (by omega))]

/-- The path in a tree of height `h` hashes only at levels 1 to `h - 1`. -/
theorem path_congr (hash' : Nat → Nat → α → α → m α) (leaves : Nat → m α) (h j : Nat)
    (agree : ∀ k, 1 ≤ k → k < h → hash k = hash' k) : path hash leaves h j = path hash' leaves h j :=
  siblings_congr hash hash' leaves h 0 j (by simpa using agree)

/-- A climb from `level` over `n` siblings hashes only at levels `level + 1` to `level + n`. -/
theorem climb_congr (hash' : Nat → Nat → α → α → m α) :
    ∀ (siblings : List α) (level j : Nat) (current : α),
      (∀ k, level < k → k ≤ level + siblings.length → hash k = hash' k) →
        climb hash level j current siblings = climb hash' level j current siblings
  | [], _, _, _, _ => rfl
  | sibling :: rest, level, j, current, agree => by
    -- This step hashes at `level + 1`, and the rest of the climb above it.
    simp only [climb, agree (level + 1) (by omega) (by simp)]
    exact congrArg _ (funext fun parent => climb_congr hash' rest (level + 1) (j / 2) parent
      (fun k h1 h2 => agree k (by omega) (by simp; omega)))

/-- A node depends on its index only modulo `N`, when the leaves and the node hash do. -/
theorem node_mod (leaves : Nat → m α) (N : Nat) (hleaves : ∀ j, leaves j = leaves (j % N))
    (hhash : ∀ level j, hash level j = hash level (j % N)) :
    ∀ (level j : Nat), node hash leaves level j = node hash leaves level (j % N) := by
  -- Two indices equal modulo `N` have children equal modulo `N`.
  suffices h : ∀ level j j', j % N = j' % N → node hash leaves level j = node hash leaves level j'
    from fun level j => h level j (j % N) (Nat.mod_mod j N).symm
  intro level
  induction level with
  | zero => intro j j' hj; rw [node_zero, node_zero, hleaves, hj, ← hleaves]
  | succ level ih =>
    intro j j' hj
    rw [node_succ, node_succ, ih (2 * j) (2 * j') (by rw [Nat.mul_mod, hj, ← Nat.mul_mod]),
      ih (2 * j + 1) (2 * j' + 1) (by rw [Nat.add_mod, Nat.mul_mod, hj, ← Nat.mul_mod,
        ← Nat.add_mod]), hhash, hj, ← hhash]

/-- A property kept by `bind` that holds of the leaves and of the node hash holds of every node. -/
theorem node_rec (P : ∀ {β : Type}, m β → Prop)
    (bind : ∀ {β γ : Type} {x : m β} {f : β → m γ}, P x → (∀ b, P (f b)) → P (x >>= f))
    (leaves : Nat → m α) (hleaves : ∀ j, P (leaves j))
    (hhash : ∀ level j left right, P (hash level j left right)) :
    ∀ (level j : Nat), P (node hash leaves level j)
  | 0, j => hleaves j
  | level + 1, j => by
    rw [node_succ]
    exact bind (node_rec P bind leaves hleaves hhash level _) fun _ =>
      bind (node_rec P bind leaves hleaves hhash level _) fun _ => hhash _ _ _ _

/-- A property kept by `pure` and `bind`, and true of the leaves and the hash, holds of siblings. -/
theorem siblings_rec (P : ∀ {β : Type}, m β → Prop) (hpure : ∀ {β : Type} (b : β), P (pure b))
    (hbind : ∀ {β γ : Type} {x : m β} {f : β → m γ}, P x → (∀ b, P (f b)) → P (x >>= f))
    (leaves : Nat → m α) (hleaves : ∀ j, P (leaves j))
    (hhash : ∀ level j left right, P (hash level j left right)) :
    ∀ (level j n : Nat), P (siblings hash leaves level j n)
  | _, _, 0 => hpure _
  | level, j, n + 1 =>
    hbind (node_rec hash P hbind leaves hleaves hhash level _) fun _ =>
      hbind (siblings_rec P hpure hbind leaves hleaves hhash (level + 1) (j / 2) n) fun _ =>
        hpure _

section Map

variable {n : Type → Type} [Monad n] (φ : ∀ {β : Type}, m β → n β)
  (map_pure : ∀ {β : Type} (b : β), φ (pure b) = pure b)
  (map_bind : ∀ {β γ : Type} (x : m β) (f : β → m γ), φ (x >>= f) = φ x >>= fun b => φ (f b))

include map_bind

/-- A map of monads that keeps `pure` and `bind` sends a node to the node of the mapped hash. -/
theorem node_map (leaves : Nat → m α) :
    ∀ (level j : Nat), φ (node hash leaves level j) =
      node (fun level j left right => φ (hash level j left right)) (fun j => φ (leaves j)) level j
  | 0, _ => rfl
  | level + 1, j => by
    simp only [node_succ, map_bind, node_map leaves level]

include map_pure in
/-- A map of monads that keeps `pure` and `bind` sends the siblings to those of the mapped tree. -/
theorem siblings_map (leaves : Nat → m α) :
    ∀ (level j n : Nat), φ (siblings hash leaves level j n) =
      siblings (fun level j left right => φ (hash level j left right)) (fun j => φ (leaves j))
        level j n
  | _, _, 0 => map_pure _
  | level, j, n + 1 => by
    simp only [siblings, map_bind, map_pure, node_map hash φ map_bind leaves, siblings_map leaves]

include map_pure in
/-- A map of monads that keeps `pure` and `bind` sends a path to the path of the mapped tree. -/
theorem path_map (leaves : Nat → m α) (h j : Nat) :
    φ (path hash leaves h j) =
      path (fun level j left right => φ (hash level j left right)) (fun j => φ (leaves j)) h j :=
  siblings_map hash φ map_pure map_bind leaves 0 j h

include map_pure in
/-- A map of monads that keeps `pure` and `bind` sends a climb to the climb of the mapped hash. -/
theorem climb_map_monad :
    ∀ (siblings : List α) (level j : Nat) (current : α), φ (climb hash level j current siblings) =
      climb (fun level j left right => φ (hash level j left right)) level j current siblings
  | [], _, _, _ => map_pure _
  | _ :: rest, level, j, current => by
    simp only [climb, map_bind, climb_map_monad rest]

end Map

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
            (ordered j current sibling).2).run rest).run :=
  rfl

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

/-- The siblings of `n + 1` ancestors are those of the first `n`, then the sibling of the next. -/
theorem siblings_succ_toList_concat (leaves : Nat → Id α) :
    ∀ n level j,
      (siblings hash leaves level j (n + 1)).run.toList
        = (siblings hash leaves level j n).run.toList
            ++ [(node hash leaves (level + n) ((j / 2 ^ n) ^^^ 1)).run]
  | 0, level, j => by simp [siblings]
  | n + 1, level, j => by
    -- Peel the first sibling on both sides, then go on one level up.
    conv => lhs; rw [siblings_succ_toList, siblings_succ_toList_concat leaves n (level + 1) (j / 2)]
    rw [siblings_succ_toList, List.cons_append, div_two_div_pow, Nat.add_assoc, Nat.add_comm 1 n]

/-- The siblings of the ancestors of leaf `j`, read one per level, start with its first siblings. -/
theorem ofFn_take_siblings (leaves : Nat → Id α) (j h : Nat) :
    ∀ n, n ≤ h → (List.ofFn fun level : Fin h =>
        (node hash leaves level ((j / 2 ^ level.val) ^^^ 1)).run).take n =
      (siblings hash leaves 0 j n).run.toList
  | 0, _ => by simp [siblings]
  | n + 1, hn => by
    rw [siblings_succ_toList_concat, ← ofFn_take_siblings leaves j h n (by omega),
      List.take_add_one]
    simp [show n < h by omega]

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

/-- The top two nodes below the root, in order, from a path of a tree of height `n + 1`.

The climb over the first `n` siblings reaches the leaf's ancestor on level `n`.

The last sibling is the other node on level `n`, and bit `n` of `j` puts the two in order. -/
theorem ordered_climb_path_last (leaves : Nat → Id α) {h n : Nat} (hn : h = n + 1) (j : Nat) :
    ordered (j / 2 ^ n)
        (climb hash 0 j (leaves j).run ((path hash leaves h j).run.toList.take n)).run
        ((path hash leaves h j).run[n]'(by omega))
      = ((node hash leaves n (2 * (j / 2 ^ n / 2))).run,
          (node hash leaves n (2 * (j / 2 ^ n / 2) + 1)).run) := by
  subst hn
  -- The path is the `n` siblings below level `n`, then the other node on level `n`.
  have hsplit := siblings_succ_toList_concat hash leaves n 0 j
  have hlength : ((siblings hash leaves 0 j n).run.toList).length = n := by simp
  rw [← Vector.getElem_toList (by simp)]
  unfold path
  simp only [hsplit, List.take_left' hlength, Nat.zero_add]
  rw [List.getElem_append_right (by simp)]
  simp only [hlength, Nat.sub_self, List.getElem_cons_zero]
  -- The climb over those siblings reaches the leaf's ancestor on level `n`.
  have hclimb := climb_siblings hash leaves n 0 j
  rw [Nat.zero_add] at hclimb
  rw [show (leaves j).run = (node hash leaves 0 j).run from rfl, hclimb]
  exact ordered_sibling (fun i => (node hash leaves n i).run) (j / 2 ^ n)

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
