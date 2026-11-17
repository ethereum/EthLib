module

public import EthLib.Cryptography.Proofs.Merkle.Position

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

variable {m : Type → Type} [Monad m] {α : Type} (hash : Position → α → α → m α)

/-- A node on level 0 is a leaf. -/
theorem node_zero (leaves : Nat → m α) (j : Nat) : node hash leaves ⟨0, j⟩ = leaves j :=
  rfl

/-- A node above level 0 hashes its two children at its own position, the left subtree first. -/
theorem node_succ (leaves : Nat → m α) (level j : Nat) :
    node hash leaves ⟨level + 1, j⟩ = (do
      let left ← node hash leaves ⟨level, 2 * j⟩
      let right ← node hash leaves ⟨level, 2 * j + 1⟩
      hash ⟨level + 1, j⟩ left right) :=
  rfl

/-- The parent of a node hashes its two children at its own position, the left subtree first. -/
theorem node_parent (leaves : Nat → m α) (p : Position) :
    node hash leaves p.parent = (do
      let left ← node hash leaves p.parent.left
      let right ← node hash leaves p.parent.right
      hash p.parent left right) :=
  rfl

/-- A node above level 0 hashes its two children at its own position, the left subtree first. -/
theorem node_children (leaves : Nat → m α) {p : Position} (hlevel : p.level ≠ 0) :
    node hash leaves p = (do
      let left ← node hash leaves p.left
      let right ← node hash leaves p.right
      hash p left right) := by
  obtain ⟨level, j⟩ := p
  cases level with
  | zero => exact absurd rfl hlevel
  | succ level => rfl

/-- Climbing two lists of siblings in turn climbs the first, then the second from where it ends. -/
theorem climb_append [LawfulMonad m] :
    ∀ (s t : List α) (p : Position) (current : α),
      climb hash p current (s ++ t) = (do
        let middle ← climb hash p current s
        climb hash (p.ancestor s.length) middle t)
  | [], t, p, current => by simp [climb]
  | sibling :: rest, t, p, current => by
    -- One level up, the rest of the climb starts at the parent.
    simp only [List.cons_append, climb, List.length_cons, bind_assoc, climb_append rest t,
      Position.ancestor_parent]

/-- Climbing the first `n + 1` siblings climbs the first `n`, then hashes in sibling `n`.

The held node is then the ancestor `n` levels up, which says which child it is. -/
theorem climb_take_succ [LawfulMonad m] (p : Position) (current : α) (s : List α) (n : Nat)
    (hn : n < s.length) :
    climb hash p current (s.take (n + 1)) = (do
      let held ← climb hash p current (s.take n)
      if (p.ancestor n).isLeft then hash (p.ancestor n).parent held s[n]
        else hash (p.ancestor n).parent s[n] held) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hn, Option.toList_some, climb_append,
    List.length_take_of_le (Nat.le_of_lt hn)]
  simp only [climb, bind_pure]
  -- The order of the children is the one the position gives.
  refine congrArg _ (funext fun held => ?_)
  unfold ordered
  split <;> rfl

/-- Ordering two mapped children maps the ordered pair. -/
theorem ordered_map {β : Type} (f : α → β) (p : Position) (current sibling : α) :
    ordered p (f current) (f sibling) = Prod.map f f (ordered p current sibling) := by
  unfold ordered
  split <;> rfl

/-- A map that commutes with the node hash commutes with the climb. -/
theorem climb_map [LawfulMonad m] {β : Type} (hash' : Position → β → β → m β) (f : α → β)
    (commute : ∀ p left right, hash' p (f left) (f right) = f <$> hash p left right) :
    ∀ (siblings : List α) (p : Position) (current : α),
      climb hash' p (f current) (siblings.map f) = f <$> climb hash p current siblings
  | [], _, _ => by simp [climb]
  | sibling :: rest, p, current => by
    simp only [List.map_cons, climb, ordered_map, Prod.map_fst, Prod.map_snd, commute,
      bind_map_left, map_bind, climb_map hash' f commute rest]

/-! ## The levels a tree hashes at -/

/-- A node hashes only at levels 1 to its own.

So two node hashes that agree there give the same node. -/
theorem node_congr (hash' : Position → α → α → m α) (leaves : Nat → m α) (p : Position)
    (agree : ∀ q : Position, 1 ≤ q.level → q.level ≤ p.level → hash q = hash' q) :
    node hash leaves p = node hash' leaves p := by
  obtain ⟨level, j⟩ := p
  induction level generalizing j with
  | zero => rfl
  | succ level ih =>
    -- The children agree by induction, and the node's own hash is at `level + 1`.
    have below : ∀ q : Position, 1 ≤ q.level → q.level ≤ level → hash q = hash' q :=
      fun q h1 h2 => agree q h1 (by simp only at *; omega)
    rw [node_succ, node_succ, ih (2 * j) below, ih (2 * j + 1) below,
      agree ⟨level + 1, j⟩ (by simp) (Nat.le_refl _)]

/-- The `n` siblings from a node up hash only at levels 1 to `level + n - 1`. -/
theorem siblings_congr (hash' : Position → α → α → m α) (leaves : Nat → m α) :
    ∀ (n : Nat) (p : Position),
      (∀ q : Position, 1 ≤ q.level → q.level < p.level + n → hash q = hash' q) →
      siblings hash leaves p n = siblings hash' leaves p n
  | 0, _, _ => rfl
  | n + 1, p, agree => by
    -- The first sibling is a node on the same level, and the rest start one level up.
    simp only [siblings]
    rw [node_congr hash hash' leaves p.sibling (fun q h1 h2 => agree q h1 (by simp at h2; omega)),
      siblings_congr hash' leaves n p.parent
        (fun q h1 h2 => agree q h1 (by simp at h2; omega))]

/-- The path in a tree of height `h` hashes only at levels 1 to `h - 1`. -/
theorem path_congr (hash' : Position → α → α → m α) (leaves : Nat → m α) (h j : Nat)
    (agree : ∀ q : Position, 1 ≤ q.level → q.level < h → hash q = hash' q) :
    path hash leaves h j = path hash' leaves h j :=
  siblings_congr hash hash' leaves h ⟨0, j⟩ (by simpa using agree)

/-- A climb from a node over `n` siblings hashes only at levels `level + 1` to `level + n`. -/
theorem climb_congr (hash' : Position → α → α → m α) :
    ∀ (siblings : List α) (p : Position) (current : α),
      (∀ q : Position, p.level < q.level → q.level ≤ p.level + siblings.length →
        hash q = hash' q) →
        climb hash p current siblings = climb hash' p current siblings
  | [], _, _, _ => rfl
  | sibling :: rest, p, current, agree => by
    -- This step hashes at the parent, and the rest of the climb above it.
    simp only [climb, agree p.parent (by simp) (by simp)]
    exact congrArg _ (funext fun parent => climb_congr hash' rest p.parent parent
      (fun q h1 h2 => agree q (by simp at h1; omega) (by simp at h2 ⊢; omega)))

/-- A node depends on its index only modulo `N`, when the leaves and the node hash do. -/
theorem node_mod (leaves : Nat → m α) (N : Nat) (hleaves : ∀ j, leaves j = leaves (j % N))
    (hhash : ∀ level j, hash ⟨level, j⟩ = hash ⟨level, j % N⟩) :
    ∀ level j, node hash leaves ⟨level, j⟩ = node hash leaves ⟨level, j % N⟩ := by
  -- Two indices equal modulo `N` have children equal modulo `N`.
  suffices h : ∀ level j j', j % N = j' % N →
      node hash leaves ⟨level, j⟩ = node hash leaves ⟨level, j'⟩
    from fun level j => h level j (j % N) (Nat.mod_mod j N).symm
  intro level
  induction level with
  | zero => intro j j' hj; rw [node_zero, node_zero, hleaves, hj, ← hleaves]
  | succ level ih =>
    intro j j' hj
    rw [node_succ, node_succ, ih (2 * j) (2 * j') (by rw [Nat.mul_mod, hj, ← Nat.mul_mod]),
      ih (2 * j + 1) (2 * j' + 1) (by rw [Nat.add_mod, Nat.mul_mod, hj, ← Nat.mul_mod,
        ← Nat.add_mod]), hhash (level + 1) j, hhash (level + 1) j']
    simp only [hj]

/-- A property kept by `bind` that holds of the leaves and of the node hash holds of every node. -/
theorem node_rec (P : ∀ {β : Type}, m β → Prop)
    (bind : ∀ {β γ : Type} {x : m β} {f : β → m γ}, P x → (∀ b, P (f b)) → P (x >>= f))
    (leaves : Nat → m α) (hleaves : ∀ j, P (leaves j))
    (hhash : ∀ p left right, P (hash p left right)) :
    ∀ p : Position, P (node hash leaves p) := by
  rintro ⟨level, j⟩
  induction level generalizing j with
  | zero => exact hleaves j
  | succ level ih =>
    rw [node_succ]
    exact bind (ih _) fun _ => bind (ih _) fun _ => hhash _ _ _

/-- A property kept by `pure` and `bind`, and true of the leaves and the hash, holds of siblings. -/
theorem siblings_rec (P : ∀ {β : Type}, m β → Prop) (hpure : ∀ {β : Type} (b : β), P (pure b))
    (hbind : ∀ {β γ : Type} {x : m β} {f : β → m γ}, P x → (∀ b, P (f b)) → P (x >>= f))
    (leaves : Nat → m α) (hleaves : ∀ j, P (leaves j))
    (hhash : ∀ p left right, P (hash p left right)) :
    ∀ (p : Position) (n : Nat), P (siblings hash leaves p n)
  | _, 0 => hpure _
  | p, n + 1 =>
    hbind (node_rec hash P hbind leaves hleaves hhash _) fun _ =>
      hbind (siblings_rec P hpure hbind leaves hleaves hhash p.parent n) fun _ =>
        hpure _

section Map

variable {n : Type → Type} [Monad n] (φ : ∀ {β : Type}, m β → n β)
  (map_pure : ∀ {β : Type} (b : β), φ (pure b) = pure b)
  (map_bind : ∀ {β γ : Type} (x : m β) (f : β → m γ), φ (x >>= f) = φ x >>= fun b => φ (f b))

include map_bind

/-- A map of monads that keeps `pure` and `bind` sends a node to the node of the mapped hash. -/
theorem node_map (leaves : Nat → m α) :
    ∀ p : Position, φ (node hash leaves p) =
      node (fun p left right => φ (hash p left right)) (fun j => φ (leaves j)) p := by
  rintro ⟨level, j⟩
  induction level generalizing j with
  | zero => rfl
  | succ level ih => simp only [node_succ, map_bind, ih]

include map_pure in
/-- A map of monads that keeps `pure` and `bind` sends the siblings to those of the mapped tree. -/
theorem siblings_map (leaves : Nat → m α) :
    ∀ (p : Position) (n : Nat), φ (siblings hash leaves p n) =
      siblings (fun p left right => φ (hash p left right)) (fun j => φ (leaves j)) p n
  | _, 0 => map_pure _
  | p, n + 1 => by
    simp only [siblings, map_bind, map_pure, node_map hash φ map_bind leaves, siblings_map leaves]

include map_pure in
/-- A map of monads that keeps `pure` and `bind` sends a path to the path of the mapped tree. -/
theorem path_map (leaves : Nat → m α) (h j : Nat) :
    φ (path hash leaves h j) =
      path (fun p left right => φ (hash p left right)) (fun j => φ (leaves j)) h j :=
  siblings_map hash φ map_pure map_bind leaves ⟨0, j⟩ h

include map_pure in
/-- A map of monads that keeps `pure` and `bind` sends a climb to the climb of the mapped hash. -/
theorem climb_map_monad :
    ∀ (siblings : List α) (p : Position) (current : α), φ (climb hash p current siblings) =
      climb (fun p left right => φ (hash p left right)) p current siblings
  | [], _, _ => map_pure _
  | _ :: rest, p, current => by
    simp only [climb, map_bind, climb_map_monad rest]

end Map

end Monad

/-! ## Unfolding, in the identity monad -/

variable {α : Type} (hash : Position → α → α → Id α)

/-- A node above level 0 is the hash of its two children, at its own position. -/
theorem node_succ_run (leaves : Nat → Id α) (level j : Nat) :
    (node hash leaves ⟨level + 1, j⟩).run
      = (hash ⟨level + 1, j⟩ (node hash leaves ⟨level, 2 * j⟩).run
          (node hash leaves ⟨level, 2 * j + 1⟩).run).run :=
  rfl

/-- The parent of a node is the hash of its two children, at its own position. -/
theorem node_parent_run (leaves : Nat → Id α) (p : Position) :
    (node hash leaves p.parent).run
      = (hash p.parent (node hash leaves p.parent.left).run
          (node hash leaves p.parent.right).run).run :=
  rfl

/-- A node above level 0 is the hash of its two children, at its own position. -/
theorem node_children_run (leaves : Nat → Id α) {p : Position} (hlevel : p.level ≠ 0) :
    (node hash leaves p).run
      = (hash p (node hash leaves p.left).run (node hash leaves p.right).run).run := by
  rw [node_children hash leaves hlevel]
  rfl

/-- The siblings start with the sibling of the node, then go on one level up. -/
theorem siblings_succ_toList (leaves : Nat → Id α) (p : Position) (n : Nat) :
    (siblings hash leaves p (n + 1)).run.toList
      = (node hash leaves p.sibling).run :: (siblings hash leaves p.parent n).run.toList := by
  simp [siblings, Vector.toList_cast]

/-- Climbing with no sibling stays put. -/
@[simp] theorem climb_nil (p : Position) (current : α) :
    (climb hash p current []).run = current :=
  rfl

/-- The pair of children determines the held node and its sibling. -/
theorem ordered_inj {p : Position} {c s c' s' : α} :
    ordered p c s = ordered p c' s' ↔ c = c' ∧ s = s' := by
  unfold ordered
  split <;> simp only [Prod.mk.injEq, and_comm]

/-- One climb step: hash the children in order at the parent's position, then go on from there. -/
theorem climb_cons (p : Position) (current sibling : α) (rest : List α) :
    (climb hash p current (sibling :: rest)).run
      = (climb hash p.parent
          (hash p.parent (ordered p current sibling).1 (ordered p current sibling).2).run
            rest).run :=
  rfl

/-! ## Completeness -/

/-- A node and its sibling, in order, are the two children of their parent.

Here `f` reads the nodes of a tree. -/
theorem ordered_sibling (f : Position → α) (p : Position) :
    ordered p (f p) (f p.sibling) = (f p.parent.left, f p.parent.right) := by
  unfold ordered
  cases h : p.isLeft
  · -- A right child has its sibling on the left.
    have hs : p.sibling.isLeft = true := by simp [h]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Position.parent_right_of_not_isLeft h, ← Position.sibling_parent,
      Position.parent_left_of_isLeft hs]
  · -- A left child has its sibling on the right.
    have hs : p.sibling.isLeft = false := by simp [h]
    simp only [↓reduceIte]
    rw [Position.parent_left_of_isLeft h, ← Position.sibling_parent,
      Position.parent_right_of_not_isLeft hs]

/-- The siblings of `n + 1` ancestors are those of the first `n`, then the sibling of the next. -/
theorem siblings_succ_toList_concat (leaves : Nat → Id α) :
    ∀ (n : Nat) (p : Position),
      (siblings hash leaves p (n + 1)).run.toList
        = (siblings hash leaves p n).run.toList
            ++ [(node hash leaves (p.ancestor n).sibling).run]
  | 0, p => by simp [siblings]
  | n + 1, p => by
    -- Peel the first sibling on both sides, then go on one level up.
    conv => lhs; rw [siblings_succ_toList, siblings_succ_toList_concat leaves n p.parent]
    rw [siblings_succ_toList, List.cons_append, Position.ancestor_parent]

/-- The siblings of the ancestors of a node, read one per level, start with its first siblings. -/
theorem ofFn_take_siblings (leaves : Nat → Id α) (p : Position) (h : Nat) :
    ∀ n, n ≤ h → (List.ofFn fun k : Fin h =>
        (node hash leaves (p.ancestor k.val).sibling).run).take n =
      (siblings hash leaves p n).run.toList
  | 0, _ => by simp [siblings]
  | n + 1, hn => by
    rw [siblings_succ_toList_concat, ← ofFn_take_siblings leaves p h n (by omega),
      List.take_add_one]
    simp [show n < h by omega]

/-- Climbing from a node with the siblings of its ancestors reaches its ancestor `n` levels up. -/
theorem climb_siblings (leaves : Nat → Id α) :
    ∀ (n : Nat) (p : Position),
      (climb hash p (node hash leaves p).run (siblings hash leaves p n).run.toList).run
        = (node hash leaves (p.ancestor n)).run := by
  intro n
  induction n with
  | zero => intro p; simp [siblings]
  | succ n ih =>
    intro p
    -- The held node and its sibling are the children of the parent, so the step reaches it.
    rw [siblings_succ_toList, climb_cons, ordered_sibling (fun q => (node hash leaves q).run)]
    dsimp only
    rw [← node_parent_run hash leaves p, ih, Position.ancestor_parent]

/-- Climbing from leaf `j` with its path reaches its ancestor on level `h`. -/
theorem climb_path (leaves : Nat → Id α) (h j : Nat) :
    (climb hash ⟨0, j⟩ (leaves j).run (path hash leaves h j).run.toList).run
      = (node hash leaves ⟨h, j / 2 ^ h⟩).run := by
  have := climb_siblings hash leaves h ⟨0, j⟩
  simp only [Position.ancestor, Nat.zero_add] at this
  exact this

/-- The top two nodes below the root, in order, from a path of a tree of height `n + 1`.

The climb over the first `n` siblings reaches the leaf's ancestor on level `n`.

The last sibling is the other node on level `n`.

The ancestor's position puts the two in order. -/
theorem ordered_climb_path_last (leaves : Nat → Id α) {h n : Nat} (hn : h = n + 1) (j : Nat) :
    ordered ⟨n, j / 2 ^ n⟩
        (climb hash ⟨0, j⟩ (leaves j).run ((path hash leaves h j).run.toList.take n)).run
        ((path hash leaves h j).run[n]'(by omega))
      = ((node hash leaves (Position.parent ⟨n, j / 2 ^ n⟩).left).run,
          (node hash leaves (Position.parent ⟨n, j / 2 ^ n⟩).right).run) := by
  subst hn
  -- The path is the `n` siblings below level `n`, then the other node on level `n`.
  have hsplit := siblings_succ_toList_concat hash leaves n ⟨0, j⟩
  have hlength : ((siblings hash leaves ⟨0, j⟩ n).run.toList).length = n := by simp
  rw [← Vector.getElem_toList (by simp)]
  unfold path
  simp only [hsplit, List.take_left' hlength]
  rw [List.getElem_append_right (by simp)]
  simp only [hlength, Nat.sub_self, List.getElem_cons_zero]
  -- The climb over those siblings reaches the leaf's ancestor on level `n`.
  have hclimb := climb_siblings hash leaves n ⟨0, j⟩
  have hanc : (⟨0, j⟩ : Position).ancestor n = ⟨n, j / 2 ^ n⟩ := by
    ext <;> simp
  rw [hanc] at hclimb
  rw [show (leaves j).run = (node hash leaves ⟨0, j⟩).run from rfl, hclimb, hanc]
  exact ordered_sibling (fun q => (node hash leaves q).run) ⟨n, j / 2 ^ n⟩

/-- Completeness: climbing from a leaf `j < 2^h` with its path reaches the root. -/
theorem climb_path_root (leaves : Nat → Id α) {h j : Nat} (hj : j < 2 ^ h) :
    (climb hash ⟨0, j⟩ (leaves j).run (path hash leaves h j).run.toList).run
      = (root hash leaves h).run := by
  rw [climb_path, Nat.div_eq_of_lt hj]
  rfl

/-! ## Trees that ignore the position -/

/-- In a tree that hashes every node alike, a node is the root of the subtree below it.

The subtree's leaves are the `2^level` leaves under node `j`, starting at leaf `j * 2^level`. -/
theorem node_const_shift (combine : α → α → Id α) :
    ∀ (level : Nat) (leaves : Nat → Id α) (j : Nat),
      (node (fun _ => combine) leaves ⟨level, j⟩).run
        = (node (fun _ => combine) (fun t => leaves (j * 2 ^ level + t)) ⟨level, 0⟩).run := by
  intro level
  induction level with
  | zero => intro leaves j; simp [node, nodeAt]
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
