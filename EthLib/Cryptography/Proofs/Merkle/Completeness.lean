module

public import EthLib.Cryptography.Proofs.Merkle.Position

/-!
# Proofs: completeness of Merkle trees

Completeness: climbing from a leaf with its path reaches the root.

The statements hold for every node hash, run in the identity monad.

The unfolding equations of a node hold in every monad.

The file also proves the facts other proofs use to move a tree between hashes and monads.
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

/-- At any position above level 0, a node hashes its left child, then its right child.

The previous equation needs the level written as `level + 1`.

This one takes any position, with a hypothesis that it is above the leaves. -/
theorem node_children (leaves : Nat → m α) {p : Position} (hlevel : p.level ≠ 0) :
    node hash leaves p = (do
      let left ← node hash leaves p.left
      let right ← node hash leaves p.right
      hash p left right) := by
  -- A position above level 0 has a level of the form `level + 1`.
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

After `n` steps the climb holds a node at the position `n` levels up.

The parity of that position says whether the node is the left or the right child. -/
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

/-- A climb step puts the node it holds on the left when its index is even. -/
theorem ordered_eq_ite (p : Position) (current sibling : α) :
    ordered p current sibling
      = if p.index % 2 = 0 then (current, sibling) else (sibling, current) := by
  unfold ordered
  simp only [Position.isLeft_iff]

/-- Two climb steps that hold nodes on opposite sides and hash the same pair swap their roles.

The node one step holds is the sibling of the other, and the other way around. -/
theorem ordered_cross {p q : Position} (hleft : p.isLeft ≠ q.isLeft) {c s c' s' : α}
    (h : ordered p c s = ordered q c' s') : c = s' ∧ s = c' := by
  unfold ordered at h
  cases hp : p.isLeft <;> cases hq : q.isLeft <;> simp_all [Prod.mk.injEq]

/-- A climb from a leaf over `n + 1` path entries climbs `n`, then hashes in entry `n`.

The bit `n` of the leaf index says whether the held node is the right child. -/
theorem climb_ofFn_succ [LawfulMonad m] (j : Nat) (path : Nat → α) (n : Nat) (value : α) :
    climb hash ⟨0, j⟩ value (List.ofFn fun level : Fin (n + 1) => path level.val) = (do
      let current ← climb hash ⟨0, j⟩ value (List.ofFn fun level : Fin n => path level.val)
      if j.testBit n then hash ⟨n + 1, j / 2 ^ (n + 1)⟩ (path n) current
      else hash ⟨n + 1, j / 2 ^ (n + 1)⟩ current (path n)) := by
  rw [List.ofFn_succ_last, climb_append, List.length_ofFn]
  refine bind_congr fun current => ?_
  -- The last step hashes at the ancestor's parent, in the order its parity gives.
  simp only [climb, bind_pure, Position.ancestor_mk_zero, Position.parent_mk, div_pow_div_two,
    ordered_eq_ite, Fin.val_last, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (j / 2 ^ n) with h | h <;> simp [h]

/-- A climb from a leaf over `n + 1` path entries climbs `n`, then takes the step from level `n`.

That step holds the node `n` levels above the leaf and hashes it with entry `n` into its parent. -/
theorem climb_ofFn_succ_ordered [LawfulMonad m] (j : Nat) (path : Nat → α) (n : Nat) (value : α) :
    climb hash ⟨0, j⟩ value (List.ofFn fun level : Fin (n + 1) => path level.val) = (do
      let current ← climb hash ⟨0, j⟩ value (List.ofFn fun level : Fin n => path level.val)
      let children := ordered ((⟨0, j⟩ : Position).ancestor n) current (path n)
      hash ((⟨0, j⟩ : Position).ancestor n).parent children.1 children.2) := by
  rw [List.ofFn_succ_last, climb_append, List.length_ofFn]
  simp only [climb, bind_pure, Fin.val_last, Fin.val_castSucc]

/-- Ordering two mapped children maps the ordered pair.

The order depends only on the position, not on the values. -/
theorem ordered_map {β : Type} (f : α → β) (p : Position) (current sibling : α) :
    ordered p (f current) (f sibling) = Prod.map f f (ordered p current sibling) := by
  -- In both cases of the parity, the map is applied to each component.
  unfold ordered
  split <;> rfl

/-- A map that commutes with the node hash at the ancestors a climb hashes at commutes with it.

For example, a node hash may agree with another only on the positions inside a tree. -/
theorem climb_map_ancestors [LawfulMonad m] {β : Type} (hash' : Position → β → β → m β)
    (f : α → β) :
    ∀ (siblings : List α) (p : Position) (current : α),
      (∀ k, 1 ≤ k → k ≤ siblings.length → ∀ left right,
        hash' (p.ancestor k) (f left) (f right) = f <$> hash (p.ancestor k) left right) →
      climb hash' p (f current) (siblings.map f) = f <$> climb hash p current siblings
  | [], _, _, _ => by simp [climb]
  | sibling :: rest, p, current, commute => by
    -- The first step hashes at the parent, the ancestor one level up.
    have hstep := commute 1 (Nat.le_refl 1) (by simp)
    simp only [Position.ancestor_one] at hstep
    simp only [List.map_cons, climb, ordered_map, Prod.map_fst, Prod.map_snd, hstep,
      bind_map_left, map_bind]
    -- The rest of the climb hashes at the parent's ancestors, one level higher each.
    refine congrArg _ (funext fun parent => climb_map_ancestors hash' f rest p.parent parent
      fun k hk1 hk2 => ?_)
    rw [Position.ancestor_parent]
    exact commute (k + 1) (by omega) (by simp; omega)

/-- A map that commutes with the node hash commutes with the climb.

For example, the map can encode nodes as bytes, for a hash defined on bytes. -/
theorem climb_map [LawfulMonad m] {β : Type} (hash' : Position → β → β → m β) (f : α → β)
    (commute : ∀ p left right, hash' p (f left) (f right) = f <$> hash p left right)
    (siblings : List α) (p : Position) (current : α) :
    climb hash' p (f current) (siblings.map f) = f <$> climb hash p current siblings :=
  climb_map_ancestors hash hash' f siblings p current fun k _ _ => commute (p.ancestor k)

/-! ## The levels a tree hashes at

Which levels a node, a path or a climb hashes at, so a hash can be changed elsewhere.
-/

/-- A node hashes only at levels 1 to its own.

So two node hashes that agree there give the same node.

A proof can then replace the hash at the levels a node never reaches. -/
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

/-- The `n` siblings from a node at level `l` up hash only at levels 1 to `l + n - 1`.

So two node hashes that agree there give the same siblings. -/
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

/-- The path in a tree of height `h` hashes only at levels 1 to `h - 1`.

It never computes the root, so the hash at level `h` does not matter. -/
theorem path_congr (hash' : Position → α → α → m α) (leaves : Nat → m α) (h j : Nat)
    (agree : ∀ q : Position, 1 ≤ q.level → q.level < h → hash q = hash' q) :
    path hash leaves h j = path hash' leaves h j :=
  siblings_congr hash hash' leaves h ⟨0, j⟩ (by simpa using agree)

/-- A climb from a node over `n` siblings hashes only at the `n` levels above the node.

So two node hashes that agree there give the same climb. -/
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

/-- A node depends on its index only modulo `N`, when the leaves and the node hash do.

For example, leaves indexed by a type with `N` values read a natural index modulo `N`. -/
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
    -- The children `2j` and `2j + 1` are equal modulo `N` to `2j'` and `2j' + 1`.
    rw [node_succ, node_succ, ih (2 * j) (2 * j') (by rw [Nat.mul_mod, hj, ← Nat.mul_mod]),
      ih (2 * j + 1) (2 * j' + 1) (by rw [Nat.add_mod, Nat.mul_mod, hj, ← Nat.mul_mod,
        ← Nat.add_mod]), hhash (level + 1) j, hhash (level + 1) j']
    simp only [hj]

/-- A property kept by `bind` that holds of the leaves and of the node hash holds of every node.

For example, the property can say that a computation never queries some input. -/
theorem node_rec (P : ∀ {β : Type}, m β → Prop)
    (bind : ∀ {β γ : Type} {x : m β} {f : β → m γ}, P x → (∀ b, P (f b)) → P (x >>= f))
    (leaves : Nat → m α) (hleaves : ∀ j, P (leaves j))
    (hhash : ∀ p left right, P (hash p left right)) :
    ∀ p : Position, P (node hash leaves p) := by
  rintro ⟨level, j⟩
  induction level generalizing j with
  | zero => exact hleaves j
  | succ level ih =>
    -- A node binds its two children, then hashes them.
    rw [node_succ]
    exact bind (ih _) fun _ => bind (ih _) fun _ => hhash _ _ _

/-- A property kept by `pure` and `bind`, and true of the leaves and the hash, holds of siblings.

The siblings also need `pure`, to return the vector they collect. -/
theorem siblings_rec (P : ∀ {β : Type}, m β → Prop) (hpure : ∀ {β : Type} (b : β), P (pure b))
    (hbind : ∀ {β γ : Type} {x : m β} {f : β → m γ}, P x → (∀ b, P (f b)) → P (x >>= f))
    (leaves : Nat → m α) (hleaves : ∀ j, P (leaves j))
    (hhash : ∀ p left right, P (hash p left right)) :
    ∀ (p : Position) (n : Nat), P (siblings hash leaves p n)
  | _, 0 => hpure _
  | p, n + 1 =>
    -- Compute one sibling, then the siblings one level up, then return them together.
    hbind (node_rec hash P hbind leaves hleaves hhash _) fun _ =>
      hbind (siblings_rec P hpure hbind leaves hleaves hhash p.parent n) fun _ =>
        hpure _

section Map

/-! ### Changing the monad

A map of monads that keeps `pure` and `bind` moves a computation to another monad.

For example, it can answer oracle calls from a table, or lift them into a larger oracle.

The tree commutes with such a map: mapping a node is computing the node with the mapped hash.
-/

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
  -- The map passes through each bind, down to the children and the hash.
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

/-- A node at level `level + 1` is the hash of its two children, at its own position.

It holds by definition. -/
theorem node_succ_run (leaves : Nat → Id α) (level j : Nat) :
    (node hash leaves ⟨level + 1, j⟩).run
      = (hash ⟨level + 1, j⟩ (node hash leaves ⟨level, 2 * j⟩).run
          (node hash leaves ⟨level, 2 * j + 1⟩).run).run :=
  rfl

/-- A node at any position above the leaves is the hash of its two children, at that position. -/
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

/-- The ordered pair determines the node a climb holds and its sibling.

So two climb steps at one position that hash the same pair held the same node and sibling. -/
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

Here `f` gives the node at each position, for example in the honest tree.

So a climb step from an honest node with its honest sibling hashes the parent's children. -/
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

/-- Siblings listed one per level for `h` levels, cut to the first `n`, are the first `n` siblings.

The list on the left gives sibling `k` as a function of `k`, as a signature scheme may state it. -/
theorem ofFn_take_siblings (leaves : Nat → Id α) (p : Position) (h : Nat) :
    ∀ n, n ≤ h → (List.ofFn fun k : Fin h =>
        (node hash leaves (p.ancestor k.val).sibling).run).take n =
      (siblings hash leaves p n).run.toList
  | 0, _ => by simp [siblings]
  | n + 1, hn => by
    -- Both sides grow by the sibling of the ancestor `n` levels up.
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
    rw [← node_children_run hash leaves (p := p.parent) (by simp), ih, Position.ancestor_parent]

/-- Climbing from leaf `j` with its path reaches its ancestor on level `h`.

That ancestor is the root only when `j < 2^h`. -/
theorem climb_path (leaves : Nat → Id α) (h j : Nat) :
    (climb hash ⟨0, j⟩ (leaves j).run (path hash leaves h j).run.toList).run
      = (node hash leaves ⟨h, j / 2 ^ h⟩).run := by
  -- A path is the siblings of the leaf, so this is the climb along the siblings.
  have := climb_siblings hash leaves h ⟨0, j⟩
  rwa [Position.ancestor_mk_zero] at this

/-- The last step of a climb along a path of height `n + 1` hashes the children of the top node.

The top node is the leaf's ancestor on level `n + 1`, the root when the leaf is in the tree. -/
theorem ordered_climb_path_last (leaves : Nat → Id α) {h n : Nat} (hn : h = n + 1) (j : Nat) :
    ordered ((⟨0, j⟩ : Position).ancestor n)
        (climb hash ⟨0, j⟩ (leaves j).run ((path hash leaves h j).run.toList.take n)).run
        ((path hash leaves h j).run[n]'(by omega))
      = ((node hash leaves ((⟨0, j⟩ : Position).ancestor (n + 1)).left).run,
          (node hash leaves ((⟨0, j⟩ : Position).ancestor (n + 1)).right).run) := by
  subst hn
  -- The path is the `n` siblings below level `n`, then the other node on level `n`.
  --
  -- That last sibling is the other child of the top node.
  have hsplit := siblings_succ_toList_concat hash leaves n ⟨0, j⟩
  have hlength : ((siblings hash leaves ⟨0, j⟩ n).run.toList).length = n := by simp
  rw [← Vector.getElem_toList (by simp)]
  unfold path
  simp only [hsplit, List.take_left' hlength]
  rw [List.getElem_append_right (by simp)]
  simp only [hlength, Nat.sub_self, List.getElem_cons_zero]
  -- The climb over those siblings reaches the leaf's ancestor on level `n`.
  have hclimb := climb_siblings hash leaves n ⟨0, j⟩
  -- The ancestor's position puts the two in order.
  rw [show (leaves j).run = (node hash leaves ⟨0, j⟩).run from rfl, hclimb,
    ordered_sibling (fun q => (node hash leaves q).run), Position.parent_ancestor]

/-- Completeness: climbing from a leaf `j < 2^h` with its path reaches the root.

So an honest path always verifies. -/
theorem climb_path_root (leaves : Nat → Id α) {h j : Nat} (hj : j < 2 ^ h) :
    (climb hash ⟨0, j⟩ (leaves j).run (path hash leaves h j).run.toList).run
      = (root hash leaves h).run := by
  -- The ancestor on level `h` has index `j / 2^h = 0`, which is the root.
  rw [climb_path, Nat.div_eq_of_lt hj]
  rfl

/-! ## Trees that ignore the position

How a tree whose hash ignores the position splits into subtrees.
-/

/-- In a tree that hashes every node alike, a node is the root of the subtree below it.

The subtree's leaves are the `2^level` leaves under node `j`, starting at leaf `j * 2^level`.

This fails when the hash reads the position, since the subtree's positions start again at 0.

So a tree such as SSZ's can be computed one subtree at a time. -/
theorem node_const_shift (combine : α → α → Id α) :
    ∀ (level : Nat) (leaves : Nat → Id α) (j : Nat),
      (node (fun _ => combine) leaves ⟨level, j⟩).run
        = (node (fun _ => combine) (fun t => leaves (j * 2 ^ level + t)) ⟨level, 0⟩).run := by
  intro level
  induction level with
  | zero => intro leaves j; simp [node_zero]
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
